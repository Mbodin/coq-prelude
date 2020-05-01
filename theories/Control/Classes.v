(* coq-prelude
 * Copyright (C) 2018 ANSSI, 2020 Martin Bodin
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

From Prelude Require Export Control Equality.

(** * Monad Transformer *)

Class MonadTrans (t : forall (m : Type -> Type), Type -> Type) : Type :=
  { monad_trans_is_monad (m : Type -> Type) `{Monad m} :> Monad (t m)
  ; lift {m} `{Monad m} (a : Type) : m a -> t m a
  }.

Arguments lift [t _ m _ a] (_%monad).

(** * State Monad *)

Class MonadState (s : Type) (m : Type -> Type) :=
  { monadstate_is_monad :> Monad m
  ; put : s -> m unit
  ; get : m s
  }.

Arguments put [s m _] _.
Arguments get {s m _}.

#[local]
Open Scope monad_scope.

Definition modify {s m} `{MonadState s m} (f : s -> s) : m unit :=
  get >>= fun x => put (f x).

Definition gets {s a m} `{MonadState s m} (f : s -> a) : m a :=
  get >>= fun x => pure (f x).

Instance monadtransform_state
  (t : forall (m : Type -> Type), Type -> Type) `{MonadTrans t}
  (s : Type) (m : Type -> Type) `{MonadState s m}
  : MonadState s (t m) :=
  { put := fun x => lift (put x)
  ; get := lift get
  }.

(** * Reader Monad *)

Class MonadReader (r : Type) (m : Type -> Type) : Type :=
  { monadreader_is_monad :> Monad m
  ; ask : m r
  }.

Arguments ask {r m _}.

Instance monadtransform_reader
  (t : forall (m: Type -> Type), Type -> Type) `{MonadTrans t}
  (r : Type) (m : Type -> Type) `{MonadReader r m}
  : MonadReader r (t m) :=
  { ask := lift ask
  }.


(** * Monad Reasonning *)

(** We introduce this structure to be able to reason about monads,
  and in particular to be able to relate a monadic interpreter with
  a usual small-step semantics.
  It is based on a special high-order predicate that transpose a
  predicate about inside the monad. **)
Class ReasonMonad m (M : Monad m) := {
    reason_predicate : forall A : Type, (A -> Prop) -> m A -> Prop ;
    reason_predicate_pure : forall A (p : A -> Prop) (a : A), p a -> reason_predicate _ p (pure a) ;
    reason_predicate_bind : forall A B (p : A -> Prop) (q : B -> Prop) (f : A -> m B) (m : m A),
      (forall a : A, p a -> reason_predicate _ q (f a)) ->
      reason_predicate _ p m ->
      reason_predicate _ q (m >>= f)%monad
  }.
Arguments ReasonMonad m {M}.

(** In particular, some monads can be reversed. **)
Class ReversibleMonad m (M : Monad m) := {
    reversible_pure : forall A (a1 a2 : A), pure a1 = pure a2 -> a1 = a2 ;
    reversible_bind : forall A B (f : A -> m B) (m : m A) (b : B),
      (m >>= f)%monad = pure b ->
      exists a, m = pure a /\ f a = pure b
  }.
Arguments ReversibleMonad m {M}.

(** Any reversible monad comes with a natural way to reason on it. **)
Instance ReversibleMonad_ReasonMonad : forall m (M : Monad m),
  ReversibleMonad m ->
  ReasonMonad m.
Proof.
  intros m M RM.
  refine {|
      reason_predicate := fun A p m => forall r, m = pure r -> p r
    |}.
  - intros A p a ? r E. apply reversible_pure in E. now subst.
  - intros A B p q f m' Rf Rp r E. apply reversible_bind in E.
    destruct E as [a [E1 E2]]. eapply Rf; [| apply E2 ]. now apply Rp.
Defined.


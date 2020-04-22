(* coq-prelude
 * Copyright (C) 2020 Martin Bodin
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

From Prelude Require Import Control Equality.

Set Implicit Arguments.

(** * Definition of the non-termination datastructure **)

(** The Non-Termination Monad, taken from Adam Chlipala’s book:
  http://adam.chlipala.net/cpdt/html/GeneralRec.html#computation **)

Section computation.

  Variable A : Type.

  Definition computation :=
    { f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v -> forall (n' : nat),
          n' >= n ->
	  f n' = Some v }.

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.

End computation.

Section Bottom.

  Variable A : Type.

  Definition Bottom : computation A.
  Proof.
    exists (fun _ : nat => @None A); abstract auto.
  Defined.

  Lemma run_Bottom : forall v, ~ run Bottom v.
  Proof.
    intros ? [? H]. inversion H.
  Qed.

End Bottom.

Section Return.

  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
  Proof.
    intros; exists (fun _ : nat => Some v); abstract auto.
  Defined.

  Lemma run_Return : run Return v.
  Proof.
    exists 0. reflexivity.
  Qed.

End Return.

Section Bind.

  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
  Proof.
    exists (fun n =>
      let (f1, _) := m1 in
      match f1 n with
      | None => None
      | Some v =>
        let (f2, _) := m2 v in
        f2 n
      end).
    abstract (
       intros n v; destruct m1 as [f1 I1], (f1 n) as [v1|] eqn: E1; [| inversion 1 ];
       intros E n' I; erewrite I1; eauto;
       destruct (m2 v1) as [f2 I2]; eauto
     ).
  Defined.

  Lemma run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1 ->
    run (m2 v1) v2 ->
    run Bind v2.
  Proof.
    intros v1 v2 [n1 R1] [n2 R2]. exists (max n1 n2).
    unfold runTo in *. simpl.
    destruct m1 as [f1 I1]. simpl in R1.
    rewrite (I1 _ _ R1); [|apply PeanoNat.Nat.le_max_l].
    destruct (m2 v1) as [f2 I2]. simpl in R2.
    rewrite (I2 _ _ R2); [|apply PeanoNat.Nat.le_max_r].
    reflexivity.
  Qed.

End Bind.

Section lattice.

  Variable A : Type.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.

  Lemma leq_refl : forall x, leq x x.
  Proof. repeat intro. auto. Qed.

End lattice.

Section Fix.

  Variables A B : Type.

  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v -> forall (v2 : A -> computation B),
      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n)) ->
      runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.

  Lemma Fix'_ok : forall steps n x v,
    proj1_sig (Fix' n x) steps = Some v -> forall n',
      n' >= n ->
      proj1_sig (Fix' n' x) steps = Some v.
  Proof.
    unfold runTo in *; induction n; simpl.
    - inversion 1.
    - intros x v E [|n'] I; [inversion I|]. apply le_S_n in I. simpl.
      eapply f_continuous; [ apply E |].
      intros y v' E'. apply IHn; auto.
  Qed.

  Definition Fix : A -> computation B.
  Proof.
    intro x; exists (fun n => proj1_sig (Fix' n x) n).
    abstract (intros; eapply Fix'_ok; eauto; destruct Fix'; eauto).
  Defined.

  Theorem run_Fix : forall x v,
    run (f Fix x) v ->
    run (Fix x) v.
  Proof.
    intros x v [n E]. exists (S n). unfold runTo in *. simpl.
    apply f_continuous with (v2 := (Fix' n)) in E.
    - destruct f as [ff fE]. eauto.
    - intros y w E1. eauto.
  Qed.
  
End Fix.


(** * Definition of the monadic structure **)

Definition apply_computation A B (f : computation (A -> B)) (m : computation A) : computation B :=
  Bind f (fun f => Bind m (fun a => Return (f a))).

Definition map_computation A B (f : A -> B) (m : computation A) : computation B :=
  Bind m (fun a => Return (f a)).

#[program]
Instance non_termination_Functor : Functor computation :=
  { map := map_computation
  }.

Next Obligation.
  destruct x as [x Hx]. simpl.
  now destruct x; constructor.
Defined.

Next Obligation.
  destruct x as [x Hx].
  now destruct x; constructor.
Defined.

#[program]
Instance non_termination_Applicative : Applicative computation :=
  { pure := Return
  ; apply := apply_computation
  }.

Next Obligation.
  destruct v as [v Hv]. simpl.
  now destruct v; constructor.
Defined.

Next Obligation.
  destruct u as [u Hu].
  destruct u; [|constructor].
  destruct v as [v Hv].
  destruct v; [|constructor].
  destruct w as [w Hw].
  now destruct w; constructor.
Defined.

Next Obligation.
  now constructor.
Defined.

Next Obligation.
  destruct u as [u Hu].
  now destruct u; constructor.
Defined.

Next Obligation.
  destruct x as [x Hx].
  now destruct x; constructor.
Defined.

#[program]
Instance non_termination_Monad : Monad computation := {
    bind := Bind
  }.

Next Obligation.
  destruct f as [fx Hfx]. simpl.
  now destruct fx; constructor.
Defined.

Next Obligation.
  destruct x as [x Hx]. simpl.
  now destruct x; constructor.
Defined.

Next Obligation.
  destruct f as [f Hf].
  destruct f; [|constructor].
  destruct g as [ga Hga].
  destruct ga; [|constructor].
  destruct h as [hb Hhb].
  now destruct hb; constructor.
Defined.

Next Obligation.
  destruct x as [x Hx].
  destruct x; [|constructor].
  generalize (H0 a0).
  now destruct f as [fa Hfa], f' as [f'a Hf'a].
Defined.

Next Obligation.
  destruct x as [x Hx].
  now destruct x; constructor.
Defined.


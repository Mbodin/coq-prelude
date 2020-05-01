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

From Coq Require Import Setoid.
From Equations Require Import Equations Signature.

From Prelude Require Import Control.

Local Open Scope prelude_scope.
Local Open Scope monad_scope.

Equations list_map {a b:  Type} (f:  a -> b) (l:  list a) : list b :=
list_map _ nil := nil;
list_map f (cons x r) := (f x) :: (list_map f r).

#[program]
Instance list_Functor
  : Functor list :=
  { map := @list_map
  }.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Definition list_pure
           {a:  Type}
           (x:  a)
  : list a :=
  x :: nil.

Equations concat {a:  Type} (l l':  list a) : list a :=
concat nil l' := l';
concat (cons x r) l' := x :: concat r l'.


Equations list_app {a b:  Type} (f:  list (a -> b)) (l:  list a) : list b :=
list_app (cons f r) l := concat (f <$> l) (list_app r l);
list_app nil _ := nil.

Conjecture list_conjecture_applicative_1
  : forall (a b c:  Type) `{Equality c}
           (u:      list (b -> c))
           (v:      list (a -> b))
           (w:      list a),
    list_app (list_app (list_app (list_pure compose) u) v) w
    == list_app u (list_app v w).

#[program]
Instance list_Applicative
  : Applicative (list) :=
  { pure   := @list_pure
  ; apply  := @list_app
  }.

Next Obligation.
Admitted.

Next Obligation.
  apply list_conjecture_applicative_1.
Defined.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

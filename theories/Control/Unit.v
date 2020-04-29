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

Definition const (A B : Type) (b : B) : A -> B := fun _ => b.

Arguments const [A B].

#[program]
Instance unit_Functor : Functor (const unit) := {
    map := fun _ _ _ => id
  }.

#[program]
Instance unit_Applicative : Applicative (const unit) :=
  { apply := fun _ _ _ => id
  ; pure  := fun _ => const tt
  }.

Next Obligation.
  now destruct u.
Defined.

#[program]
Instance unit_Monad : Monad (const unit) :=
  { bind := fun _ _ _ => const tt
  }.

Next Obligation.
  now destruct (f x).
Defined.

Next Obligation.
  now destruct x.
Defined.

Next Obligation.
  now destruct x.
Defined.

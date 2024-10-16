From Equations Require Import Equations.

Equations? f (n : nat) : nat :=
  f 0 := 42 ;
  f (S m) with f m := { f (S m) IH := _ }.
Proof. intros. exact IH. Defined.
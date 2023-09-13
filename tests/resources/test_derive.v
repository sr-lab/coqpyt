Require Import Coq.derive.Derive.

Derive incr
SuchThat (forall n, incr n = plus 1 n)
As incr_correct.
Proof. intros n. simpl. subst incr. reflexivity. Qed.

Inductive Le : nat -> nat -> Set :=
| LeO : forall n:nat, Le 0 n
| LeS : forall n m:nat, Le n m -> Le (S n) (S m).
Derive Inversion leminv1 with (forall n m:nat, Le (S n) m) Sort Prop.
Derive Inversion_clear leminv2 with (forall n m:nat, Le (S n) m) Sort Prop.
Derive Dependent Inversion leminv3 with (forall n m:nat, Le (S n) m) Sort Prop.
Derive Dependent Inversion_clear leminv4 with (forall n m:nat, Le (S n) m) Sort Prop.
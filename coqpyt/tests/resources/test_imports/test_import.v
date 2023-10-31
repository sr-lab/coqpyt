Require Import Coq.Unicode.Utf8.
Require Import test_import2.

Ltac reduce_eq := simpl; reflexivity.

Local Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  reduce_eq.
Qed.

Definition mult_0_plus : ∀ n m : nat,
0 + (S n * m) = S n * m.
Proof.
  intros n m.
  rewrite -> (plus_O_n (S n * m)).
  Locate test_import2.plus_O_n.
  Locate Peano.plus_O_n.
  reflexivity.
Defined.
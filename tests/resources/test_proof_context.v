Require Import Coq.Unicode.Utf8.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  simpl.
  reflexivity.
Qed.

Check plus_O_n.

Theorem mult_0_plus : ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.
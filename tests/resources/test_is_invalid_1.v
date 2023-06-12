Require Import Coq.Unicode.Utf8.

Ltac reduce_eq := simpl; reflexivity.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  reduce_eq.
Qed.

Theorem mult_0_plus : ∀ n m : nat,
  0 + (S n * m) = S n * m.
Proof.
  (* intros n m. *)
  rewrite -> plus_O_n.
  Compute True /\ True.
  reflexivity.
Qed.

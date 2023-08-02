Ltac reduce_eq := simpl; reflexivity.

Local Theorem plus_O_n : forall n:nat, 0 + 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  reduce_eq.
Qed.
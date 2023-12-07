Ltac reduce_eq := simpl; reflexivity.

Local Theorem plus_O_n : forall n:nat, 0 + 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  reduce_eq.
Qed.

Definition mult_0_plus : forall n m : nat,
0 + 0 + (S n * m) = S n * m.
Proof.
  intros n m.
  rewrite -> (plus_O_n (S n * m)).
  reflexivity.
Defined.
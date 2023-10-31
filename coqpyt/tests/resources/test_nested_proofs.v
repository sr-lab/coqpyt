Set Nested Proofs Allowed.

Theorem mult_0_plus : forall n m : nat,
S n * m = 0 + (S n * m).
Proof.
intros n m.

    Theorem plus_O_n : forall n:nat, n = 0 + n.
    intros n.
    simpl; reflexivity.
    Qed.

rewrite <- (plus_O_n ((S n) * m)).
reflexivity.
Qed.

Theorem plus_O_n_2 : forall n:nat, n = 0 + n.
    intros n.
    simpl; reflexivity.
Theorem plus_O_n_3 : forall n:nat, n = 0 + n.
    intros n.
    simpl; reflexivity.
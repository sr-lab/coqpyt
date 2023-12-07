Definition x := 0.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
    intros n.
    reflexivity.
Qed.
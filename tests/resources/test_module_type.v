Module Type TestModuleType.
    Module TestModuleType.
    End TestModuleType.

    Parameter NAT_MIN : nat.
    Definition x := 2.
    
    Theorem plus_O_n_new : forall n:nat, 0 + n = n.
    Proof.
    intros n.
    simpl; reflexivity.
    Qed.
End TestModuleType.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
intros n.
simpl; reflexivity.
Qed.
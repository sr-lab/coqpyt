Theorem bullets: forall x y: nat, x = x /\ y = y.
Proof.
    intros x y. split.
    -reflexivity.
    - reflexivity.
Qed.

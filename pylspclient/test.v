Lemma kek a b c :
    a < b ->
    b = c ->
    a < c.
Proof.
    intros Hlt Heq.
    subst. assumption.
Qed.
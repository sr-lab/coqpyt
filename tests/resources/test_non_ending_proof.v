Theorem x : forall n:nat, n=n.
intro n.
destruct (plus n 1) eqn:Y.
reflexivity.
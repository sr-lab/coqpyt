Inductive binder := BAnon | BNum :> nat -> binder.
Declare Scope binder_scope.
Notation "<>" := BAnon : binder_scope.

Open Scope binder_scope.
Lemma test : <> = <>.
Proof. reflexivity. Qed.
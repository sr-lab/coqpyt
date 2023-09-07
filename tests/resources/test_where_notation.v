Reserved Notation "A & B" (at level 80).
Reserved Notation "'ONE'" (at level 80).

Fixpoint plus_test (n m : nat) {struct n} : nat :=
match n with
    | O => m
    | S p => S (p + m)
end
where "n + m" := (plus n m) : test_scope and "n - m" := (minus n m).

Inductive and' (A B : Prop) : Prop := conj' : A -> B -> A & B
where "A & B" := (and' A B).

Fixpoint incr (n : nat) : nat := n + ONE
where "'ONE'" := 1.
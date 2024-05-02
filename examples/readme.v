Require Import Coq.Unicode.Utf8.
Require Import List.

Ltac reduce_eq := simpl; reflexivity.

Theorem mult_0_plus : ∀ n m : nat, 0 + (S n * m) = S n * m.
Proof.
    intros n m.
    rewrite -> (plus_O_n (S n * m)).
    reflexivity.
Qed.

Lemma rev_append: forall {a} (l1 l2: list a),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros a l1 l2. induction l1; intros. 
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1.
Admitted.
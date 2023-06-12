Require Import Coq.Unicode.Utf8.

Ltac reduce_eq := simpl; reflexivity.

Module Out.
  Module In.
    Theorem plus_O_n : forall n:nat, 0 + n = n.
    Proof.
      intros n.
      Print plus.
      Print Nat.add.
      reduce_eq.
    Qed.
  End In.
End Out.

Theorem mult_0_plus : ∀ n m : nat,
  0 + (S n * m) = S n * m.
Proof.
  intros n m.
  rewrite -> (plus_O_n (S n * m)).
  Compute True /\ True.
  reflexivity.
Qed.

Module Extra.
  Record example := mk_example { fst : nat; snd : nat }.

  Theorem plus_O_n : forall n:nat, n = 0 + n.
  Proof.
    intros n.
    Compute mk_example n n.
    Compute {| fst := n; snd := n |}.
    reduce_eq.
  Qed.

  Theorem mult_0_plus : ∀ n m : nat,
    S n * m = 0 + (S n * m).
  Proof.
    intros n m.
    rewrite <- (plus_O_n (S n * m)).
    Compute Out.In.plus_O_n.
    reflexivity.
  Qed.
End Extra.

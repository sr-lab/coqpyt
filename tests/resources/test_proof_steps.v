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

Print Out.In.plus_O_n.
Compute Out.In.plus_O_n.

Theorem mult_0_plus : ∀ n m : nat,
  0 + (S n * m) = S n * m.
Proof.
  intros n m.
  rewrite -> (Out.In.plus_O_n (S n * m)).
  Compute True /\ True.
  reflexivity.
Qed.

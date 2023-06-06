Require Import Coq.Unicode.Utf8.

Module Out.
  Module In.
    Theorem plus_O_n : forall n:nat, 0 + n = n.
    Proof.
      intros n.
      Print plus.
      Print Nat.add.
      simpl.
      reflexivity.
    Qed.
  End In.
End Out.

Check Out.In.plus_O_n.

Theorem mult_0_plus : ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> Out.In.plus_O_n.
  reflexivity.
Qed.

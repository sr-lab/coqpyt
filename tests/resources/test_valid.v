(* Start of test file. *)

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

Section Random.
  Definition mult_0_plus : ∀ n m : nat,
    0 + (S n * m) = S n * m.
  Proof.
    intros n m.
    rewrite -> (plus_O_n (S n * m)).
    Compute True /\ True.
    reflexivity.
  Defined.
End Random.

Module Extra.
  Module Fst.
    Record example := mk_example { fst : nat; snd : nat }.

    Theorem plus_O_n : forall n:nat, n = 0 + n.
      intros n.
      Compute mk_example n n.
      Compute Out.In.plus_O_n.
      reduce_eq.
    Qed.
  End Fst.

  Module Snd.
    Notation "| a |" := (S a) (at level 30, right associativity).
    
    Theorem mult_0_plus : ∀ n m : nat,
      S n * m = 0 + (S n * m).
    Proof.
      intros n m.
      rewrite <- (Fst.plus_O_n (|n| * m)).
      Compute {| Fst.fst := n; Fst.snd := n |}.
      reflexivity.
    Admitted.
  End Snd.
End Extra.

(* End of test file. *)
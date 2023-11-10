Require Import Coq.Unicode.Utf8.

Section Random.
  Variable (n : nat) (Hn : n <> 0).

  Definition x := 1.

  Goal ∃ (m : nat),
    S m = n.
  Proof using Hn.
    destruct n.
    + exfalso. auto.
    + eexists. auto.
  Defined.

  Goal ∃ (m : nat),
    S m = n.
  Proof with auto.
    destruct n.
    + exfalso...
    + eexists...
  Qed.

  Goal nat.
  Proof 0.
End Random.
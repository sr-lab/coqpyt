Require Import Program Arith.

Ltac dummy_tactic n e := destruct n; try reflexivity; inversion e.

Module TestObligations.

Program Definition id1 (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).
Program Definition id2 (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).
Program Definition id3 (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).
Program Definition id4 (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).

Obligation 2 of id1.
  dummy_tactic n e.
Qed.
Next Obligation of id1.
  dummy_tactic n e.
Qed.
Obligation 2 of id2 : type with reflexivity.
  dummy_tactic n e.
Qed.
Next Obligation of id2 with reflexivity.
  dummy_tactic n e.
Qed.
Next Obligation.
  dummy_tactic n e.
Qed.
Next Obligation with reflexivity.
  dummy_tactic n e.
Qed.
Obligation 1.
  dummy_tactic n e.
Qed.
Obligation 2 : type with reflexivity.
  dummy_tactic n e.
Qed.

End TestObligations.

Module Out.
Program Definition id (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).

Module In.
Program Definition id (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else pred (S n).
Obligation 1 of id with reflexivity.
  dummy_tactic n e.
Qed.
End In.

Obligation 1 of id : type.
  dummy_tactic n e.
Qed.
Obligation 2 : type.
  dummy_tactic n e.
Qed.
End Out.
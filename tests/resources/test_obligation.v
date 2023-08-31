(** Heaps and heap assertions for separation logics. *)

From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
Require Import Program Arith.

Local Open Scope Z_scope.

(** * 1. Memory heaps *)

(** A memory heap is a partial function from addresses (memory locations) 
    to values, with a finite domain. *)

Definition addr := Z.

Record heap : Type := {
  contents :> addr -> option Z;
  isfinite :  exists i, forall j, i <= j -> contents j = None
}.

Program Definition hempty : heap :=
  {| contents := fun l => None |}.

Program Definition id (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0%nat
  else S (pred n).

Obligation 2 of id.
  destruct n.
  + inversion e.
  + reflexivity.
Qed.
  
Next Obligation.
  exists 0; auto.
Qed.

Obligation 1.
  destruct n.
  - reflexivity.
  - inversion e.
Qed.

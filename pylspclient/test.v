(* Lecture 6 *)

Require Import Coq.Unicode.Utf8.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intros n.
  Print plus.
  Print Nat.add.
  simpl.
  reflexivity.
Qed.

Check plus_O_n.

Theorem plus_1_l : ∀ n:nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_0_l : ∀ n:nat, 0 * n = 0.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : ∀ n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m nEqualsM.
  rewrite nEqualsM.
  reflexivity.
Qed.

Theorem plus_id_exercise : ∀ n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  intros n m o.
  intros nEqualsM mEqualsO.
  rewrite nEqualsM, mEqualsO.
  reflexivity.
Qed.


Theorem mult_S_1 : ∀ n m : nat,
  m = 1 + n →
  m * (1 + n) = m * m.
Proof.
  intros.
  rewrite <- H.
  reflexivity.
Qed.


Theorem mult_0_plus : ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.


Theorem mult_0_0_plus : ∀ n m : nat,
  (0 + (0 + n)) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n.
  rewrite plus_O_n.
  reflexivity.
Qed.



Search (nat -> nat -> bool).
Definition beq_nat := Nat.eqb.

Print Nat.eqb.

Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  (* two cases: n=0 and n=S n'*)
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : ∀ b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative : ∀ b c, 
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    -- reflexivity.
    -- reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.



Theorem plus_1_neq_0' : ∀ n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative'' :
  ∀ b c, andb b c = andb c b.
Proof.
  intros [] []; reflexivity.
Qed.


Theorem andb_true_elim2 : ∀ b c : bool,
  andb b c = true → c = true.
Proof.
  intros b c.
  destruct c.
  - reflexivity.
  - destruct b; simpl; intros H; assumption.
      (*rewrite H. reflexivity.*)
Qed.



(* Proof by induction *)
Theorem plus_n_O_firsttry : ∀ n:nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* Base case *) reflexivity.
  - (* Inductive step *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.


Theorem plus_n_Sm : ∀ n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.















  
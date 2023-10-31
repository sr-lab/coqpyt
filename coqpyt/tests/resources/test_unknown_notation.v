(** * Ordering characters *)
From Coq Require Import Ascii Orders OrderedType.

Definition bool_compare_cont (b1 b2: bool) (k: comparison) : comparison :=
  match b1, b2 with
  | false, true => Lt
  | true, false => Gt
  | _, _ => k
  end.

Definition ascii_compare (x y: ascii) : comparison :=
  match x, y with
  | Ascii x1 x2 x3 x4 x5 x6 x7 x8, Ascii y1 y2 y3 y4 y5 y6 y7 y8 =>
      bool_compare_cont x8 y8 (
      bool_compare_cont x7 y7 (
      bool_compare_cont x6 y6 (
      bool_compare_cont x5 y5 (
      bool_compare_cont x4 y4 (
      bool_compare_cont x3 y3 (
      bool_compare_cont x2 y2 (
      bool_compare_cont x1 y1 Eq)))))))
  end.

(** Alternate presentation, using recursion over bitvectors. *)

Fixpoint bitvect (n: nat) : Type :=
  match n with O => bool | S n => (bitvect n * bool)%type end.

Fixpoint bitvect_compare (n: nat) : bitvect n -> bitvect n -> comparison :=
  match n with
  | O => (fun b1 b2 => bool_compare_cont b1 b2 Eq)
  | S n => (fun v1 v2 => bool_compare_cont (snd v1) (snd v2) (bitvect_compare n (fst v1) (fst v2)))
  end.

Lemma ascii_bitvect_compare:
  forall x y,
  ascii_compare x y =
  match x, y with
  | Ascii x1 x2 x3 x4 x5 x6 x7 x8, Ascii y1 y2 y3 y4 y5 y6 y7 y8 =>
      bitvect_compare 7%nat
        (x1, x2, x3, x4, x5, x6, x7, x8)
        (y1, y2, y3, y4, y5, y6, y7, y8)
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

Lemma bitvect_compare_refl:
  forall n x, bitvect_compare n x x = Eq.
Proof.
  induction n; simpl.
- destruct x; auto.
- intros [x x1]; simpl. rewrite IHn. destruct x1; auto.
Qed.

Lemma bitvect_compare_eq:
  forall n x y, bitvect_compare n x y = Eq -> x = y.
Proof.
  induction n; simpl.
- destruct x, y; simpl; congruence.
- intros [x x1] [y y1]; unfold bool_compare_cont; simpl; intros.
  destruct x1, y1; try discriminate; f_equal; eauto.
Qed.

Lemma bitvect_compare_lt_trans:
  forall n x y z, bitvect_compare n x y = Lt -> bitvect_compare n y z = Lt -> bitvect_compare n x z = Lt.
Proof.
  induction n; simpl.
- intros. destruct x, y; try discriminate. destruct z; discriminate.
- intros [x x1] [y y1] [z z1]; simpl; intros. 
  assert (A: forall b1 b2 k, bool_compare_cont b1 b2 k = Lt -> b1 = false /\ b2 = true \/ b1 = b2 /\ k = Lt).
  { intros. destruct b1, b2; auto; discriminate. }
  apply A in H. apply A in H0. 
  destruct H as [[P1 P2] | [P1 P2]]; destruct H0 as [[Q1 Q2] | [Q1 Q2]]; subst; subst; auto.
  erewrite IHn by eauto. destruct z1; auto.
Qed.

Lemma bitvect_compare_antisym:
  forall n x y, CompOpp (bitvect_compare n x y) = bitvect_compare n y x.
Proof.
  assert (A: forall b1 b2 k, CompOpp (bool_compare_cont b1 b2 k) = bool_compare_cont b2 b1 (CompOpp k)).
  { intros. destruct b1, b2; auto. }
  induction n; simpl.
- destruct x, y; auto.
- intros [x x1] [y y1]. simpl. rewrite A. f_equal; auto.
Qed.

Lemma ascii_compare_refl:
  forall x, ascii_compare x x = Eq.
Proof.
  intros. rewrite ascii_bitvect_compare. destruct x. apply bitvect_compare_refl.
Qed.

Lemma ascii_compare_eq:
  forall x y, ascii_compare x y = Eq -> x = y.
Proof.
  intros. rewrite ascii_bitvect_compare in H. destruct x, y.
  apply bitvect_compare_eq in H. congruence.
Qed.

Lemma ascii_compare_lt_trans:
  forall x y z, ascii_compare x y = Lt -> ascii_compare y z = Lt -> ascii_compare x z = Lt.
Proof.
  intros. rewrite ascii_bitvect_compare in *. destruct x, y, z.
  eapply bitvect_compare_lt_trans; eauto.
Qed.

Lemma ascii_compare_antisym:
  forall x y, CompOpp (ascii_compare x y) = ascii_compare y x.
Proof.
  intros. rewrite ! ascii_bitvect_compare. destruct x, y.
  apply bitvect_compare_antisym.
Qed.

(** Implementing the [OrderedType] interface *)

Module OrderedAscii <: OrderedType.

Definition t := ascii.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := ascii_compare x y = Lt.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof ascii_compare_lt_trans.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  unfold lt, eq; intros; red; intros. subst y. 
  rewrite ascii_compare_refl in H. discriminate.
Qed.

Definition compare (x y : t) : Compare lt eq x y.
Proof.
  destruct (ascii_compare x y) eqn:AC.
- apply EQ. apply ascii_compare_eq; auto.  
- apply LT. assumption.
- apply GT. red. rewrite <- ascii_compare_antisym. rewrite AC; auto.
Defined.

Definition eq_dec (x y : t) : {x = y} + {x <> y}.
Proof.
  destruct (ascii_compare x y) eqn:AC.
- left. apply ascii_compare_eq; auto.
- right; red; intros; subst y. rewrite ascii_compare_refl in AC; discriminate.
- right; red; intros; subst y. rewrite ascii_compare_refl in AC; discriminate.
Defined.

End OrderedAscii.


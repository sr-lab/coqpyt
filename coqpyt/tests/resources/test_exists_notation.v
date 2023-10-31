Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation between states *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

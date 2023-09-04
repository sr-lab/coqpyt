Class EqDecNew (A : Type) :=
  { eqb_new : A -> A -> bool ;
    eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ;
    eqb_ident_new : forall x, eqb_new x x = true }.

#[refine] Global Instance unit_EqDec : EqDecNew unit := { eqb_new x y := true }.
Proof.
  intros [] []; reflexivity.
  intros []; reflexivity.
Defined.
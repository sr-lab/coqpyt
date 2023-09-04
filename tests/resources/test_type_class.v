Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y ;
    eqb_ident : forall x, eqb x x = true }.

#[refine] Global Instance unit_EqDec : EqDec unit := { eqb x y := true }.
Proof.
  intros [] []; reflexivity.
  intros []; reflexivity.
Defined.
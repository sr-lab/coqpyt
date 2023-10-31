Module TypeClass.
Class EqDecNew (A : Type) :=
{ eqb_new : A -> A -> bool ;
  eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ;
  eqb_ident_new : forall x, eqb_new x x = true }.
End TypeClass.

#[refine] Global Instance unit_EqDec : TypeClass.EqDecNew unit := { eqb_new x y := true }.
Proof.
intros [] []; reflexivity.
intros []; reflexivity.
Defined.

Section test.

Instance test : TypeClass.EqDecNew unit -> TypeClass.EqDecNew unit.
Proof.
  auto.
Defined.

End test.
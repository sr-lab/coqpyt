Require Import Coq.Unicode.Utf8.

Module A.
    Definition x := 2.
End A.

Goal ∀ (A : nat), A = A.
Proof.
    Print A.
    reflexivity.
Qed.
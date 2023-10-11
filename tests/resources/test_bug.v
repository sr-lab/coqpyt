Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Fixpoint min (l : (list nat)) : option nat := 
    match l with
    | nil => None
    | h :: tl => match (min tl) with
        | None => Some h 
        | Some m => if (h <? m) then (Some h) else (Some m)
        end
    end.

Lemma exists_min: forall (l : (list nat)), 
    (l <> nil) -> exists h, min(l) = Some(h).
Proof.
  intros.
  induction l.
  - contradiction.
  - exists a.
    simpl.
    destruct (min l).
    + 
Admitted.
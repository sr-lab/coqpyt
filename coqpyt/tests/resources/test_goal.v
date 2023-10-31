(* http://d.hatena.ne.jp/hzkr/20100902 *)

Definition ignored : forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  intros.  (* 全部剥がす *)
  apply H.
  exact H0.  (* apply H0 でも同じ *)
Save opaque.


Goal forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  intros p q f.  (* 名前の数だけ剥がす *)
  assumption.  (* exact f でも同じ *)
Qed.


Goal forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  exact (fun p q f x => f x).
Defined transparent.
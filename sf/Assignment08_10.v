Require Export Assignment08_09.

(* problem #10: 10 points *)

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
intros. split.
{ intros. inversion H. subst. inversion H2. subst. apply E_Seq with st'1. apply H3. apply E_Seq with st'0. apply H7. apply H5. }
{ intros. inversion H. inversion H5. subst. apply E_Seq with st'1.  apply E_Seq with st'0. apply H2. apply H8. apply H11. }
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).


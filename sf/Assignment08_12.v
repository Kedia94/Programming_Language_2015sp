Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
intros c1 c1' c2 c2' H1 H2. split.
{ intro H3. inversion H3. subst. apply E_Seq with st'0. apply H1. apply H4. apply H2. apply H7. }
{ intros H3. inversion H3. subst. apply E_Seq with st'0. apply H1. apply H4. apply H2. apply H7. }
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').


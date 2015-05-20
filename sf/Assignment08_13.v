Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
intros. split.
{ intros. inversion H2. subst. apply E_IfTrue. unfold bequiv in H. rewrite <- H8. rewrite H. reflexivity. apply H0. apply H9. subst.
  apply E_IfFalse. rewrite <- H8. rewrite H. reflexivity. apply H1. apply H9. }
{ intros. inversion H2. subst. apply E_IfTrue. rewrite <- H8. apply H. apply H0. apply H9. subst. apply E_IfFalse. rewrite <- H8. rewrite H. reflexivity. apply  H1. apply H9. }
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).


Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
assert (K: forall n1 x1 x2 (st : state), st x1 = n1 -> (update st x1 n1) x2 = st x2).
  { intros. inversion H. unfold update. remember (eq_id_dec x1 x2). destruct s. rewrite e. reflexivity. reflexivity. }
intros. split.
{ intros. inversion H0. subst. assert (st' = (update st' X (st' X))). apply functional_extensionality. intro. rewrite K. reflexivity. reflexivity.
  rewrite H1. rewrite <- H1 in |-* at 1. apply E_Ass. rewrite <- H. simpl. reflexivity. }
{ intros. inversion H0. subst. assert (st = update st X (aeval st e)). rewrite <- H. apply functional_extensionality. intros. rewrite K. reflexivity. simpl. reflexivity.
  rewrite <- H1. constructor. }
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).


Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
intros. unfold cequiv. intros. split.
{ intros. inversion H. subst. apply E_IfFalse. simpl. rewrite H5. simpl. reflexivity. apply H6. subst. apply E_IfTrue. simpl. rewrite H5. reflexivity. apply H6. }
{ intros. inversion H. subst. apply E_IfFalse. simpl in H5. apply negb_true_iff in H5. apply H5. apply H6. subst. apply E_IfTrue. simpl in H5. apply negb_false_iff in H5. apply H5. apply H6. }
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).


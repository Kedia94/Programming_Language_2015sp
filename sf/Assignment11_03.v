Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
assert (K: forall t, nvalue t -> value t). { intros. unfold value. right. apply H. }
unfold deterministic. intros. generalize dependent y2. induction H.
intros. inversion H0. reflexivity. inversion H3. inversion H4.
intros. inversion H0. reflexivity. subst. inversion H4. 
intros. inversion H0; subst. inversion H. inversion H. apply IHstep in H5. subst. reflexivity. 
intros. inversion H0. subst. apply IHstep in H2. subst; reflexivity.
intros. inversion H0. reflexivity. solve by inversion.
intros. inversion H0. reflexivity. subst. inversion H2. subst. 
  remember (value_is_nf t1). apply K in H. apply n in H. unfold normal_form in H. unfold not in H.
  assert (t1 ==> t1'0 -> (exists t': tm, t1==>t')). intros. exists t1'0. apply H1. apply H1 in H3. apply H in H3. inversion H3.
intros. inversion H0. subst. inversion H.
  apply ex_falso_quodlibet. eapply value_is_nf. apply K. apply H2. subst. inversion H. exists t1'0. apply H3.
  subst. apply IHstep in H2. subst. reflexivity.
intros. inversion H0. reflexivity. solve by inversion.
intros. inversion H0. reflexivity. subst. apply ex_falso_quodlibet. eapply value_is_nf. apply K. apply H. inversion H2. exists t1'0. apply H3.
intros. inversion H0; subst. inversion H. apply ex_falso_quodlibet. eapply value_is_nf. apply K. apply H2. inversion H. exists t1'0. apply H3. apply IHstep in H2; subst. reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.


Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
assert (K: exists Q R, tapp tloop (tnat 0) ==> Q /\ Q ==> R /\ R ==> tapp tloop (tnat 0)).
{ eapply ex_intro. eapply ex_intro. split. unfold tloop. auto. split. auto. simpl. unfold tloop. apply ST_AppAbs. trivial. }

assert (K0: forall v, value v -> (exists v', v ==> v') -> False).
{ intros. induction v; try (inversion H); subst; inversion H0; subst; try inversion H1; eauto. }

assert (K1: deterministic step).
{ unfold deterministic. intros. generalize dependent y2. induction H; intros.
  inversion H0. auto. solve by inversion.
  subst. exfalso. apply K0 with v2. auto. exists t2'. auto.
  inversion H0. eauto. solve by inversion 2. apply IHstep in H4. subst. auto.
  subst. exfalso. apply K0 with t1. auto. exists t1'. auto. subst. inversion H; subst. exfalso. apply K0 with F1.
  auto. exists t1'0. auto.
  inversion H1. exfalso. apply K0 with t2. auto. eauto. exfalso. apply K0 with v1. auto. eauto. apply IHstep in H6.
  subst. eauto. subst. inversion H1. inversion H3. subst. exfalso. apply K0 with t2. auto. eauto.
  inversion H0. apply IHstep in H2. subst; auto. subst. inversion H.
  inversion H0. inversion H1. subst. auto.
  inversion H0. apply IHstep in H2. subst. auto. subst. inversion H.
  inversion H0. inversion H1. subst. inversion H0. auto.
  inversion H0; subst. apply IHstep in H4; subst. auto. exfalso. apply K0 with t1. eauto. eauto.
  inversion H.
  inversion H1; subst. exfalso. apply K0 with v1. eauto. eauto.
  apply IHstep in H6. subst. auto.
  inversion H0.
  inversion H0. inversion H3. inversion H4. auto.
  inversion H0. apply IHstep in H5. subst. auto.
  subst. inversion H. subst. inversion H. inversion H0. inversion H4. auto. inversion H0. inversion H4. auto.
  inversion H0. apply IHstep in H4. subst. auto. exfalso. apply K0 with t1. eauto. eauto.
  inversion H1. exfalso. apply K0 with v1. eauto. eauto. apply IHstep in H6. subst. auto.
  inversion H0. apply IHstep in H2. subst. auto. subst. inversion H. exfalso. apply K0 with y2. eauto. eauto.
  exfalso. apply K0 with v2. eauto. eauto. inversion H1. inversion H3. exfalso. apply K0 with v1. eauto. eauto.
  exfalso. apply K0 with v2. eauto. eauto. auto.
  inversion H0. apply IHstep in H2. subst. auto. subst. inversion H. exfalso. apply K0 with y2. eauto. eauto.
  exfalso. apply K0 with v1. eauto. eauto. exfalso. apply K0 with y2. eauto. eauto.
  inversion H1. inversion H3. exfalso. apply K0 with v1. eauto. eauto.
  exfalso. apply K0 with v2. eauto. eauto. eauto.
  inversion H0. apply IHstep in H5. subst. auto. exfalso. apply K0 with t1. eauto. eauto.
  inversion H0. exfalso. apply K0 with v1. eauto. eauto. auto.
  inversion H0. apply IHstep in H4. subst. eauto. inversion H0. apply IHstep in H4. subst. eauto.
  inversion H0. subst. apply IHstep in H7. subst. eauto. subst. inversion H. exfalso. apply K0 with v0. eauto. eauto.
  subst. inversion H. exfalso. apply K0 with v0. eauto. eauto.
  inversion H0; subst. inversion H7; subst. exfalso. apply K0 with v0. eauto. eauto. eauto.
  inversion H0; subst. inversion H7; subst. exfalso. apply K0 with v0. eauto. eauto. auto.
  inversion H0. apply IHstep in H4. subst; auto. exfalso. apply K0 with t1. eauto. eauto.
  inversion H1. exfalso. apply K0 with v1. eauto. eauto. apply IHstep in H6. subst; eauto.
  inversion H0; subst. apply IHstep in H7. subst. auto.
  inversion H. inversion H. exfalso. apply K0 with v1. eauto. eauto. exfalso. apply K0 with vl. eauto. exists t2'. apply H5. 
  inversion H0. inversion H6. auto.
  inversion H1; subst. inversion H8. exfalso. apply K0 with v1. eauto. eauto. exfalso. apply K0 with vl. eauto. exists t2'. apply H6.
  auto. inversion H0. apply IHstep in H2. subst; eauto. inversion H1. subst. inversion H5. exfalso. apply K0 with F1. eauto. eauto.
  exfalso. apply K0 with v2. eauto. eauto. auto. }

assert (K2: forall P Q R X, P ==> Q -> Q ==> R -> R ==> P -> P ==>* X -> (X=P \/ X=Q \/ X=R)).
{ intros. generalize dependent Q. generalize dependent R. induction H2. intros. auto.
  intros. unfold deterministic in K1. apply K1 with (y2:=Q) in H. subst.
  assert (z=Q \/ z=R \/ z=x). apply IHmulti. assumption. assumption. assumption. inversion H. auto. inversion H4. auto. auto. auto. }
unfold not. intros. destruct H. destruct H. inversion K. destruct H1. 
assert (x=tapp tloop (tnat 0) \/ x=x0 \/ x=x1). inversion H1 as [Q1 [Q2 Q3]]. apply K2; assumption.
inversion H2. apply H0. exists x0. destruct H1 as [Q1 [Q2 Q3]]. subst. apply Q1.
inversion H3. subst. apply H0. exists x1. inversion H1 as [Q1 [Q2 Q3]]. apply Q2.
subst. apply H0. exists (tapp tloop (tnat 0)). inversion H1 as [Q1 [Q2 Q3]]. apply Q3.

Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.


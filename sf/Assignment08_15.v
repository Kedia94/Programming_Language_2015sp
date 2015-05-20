Require Export Assignment08_14.

(* problem #15: 10 points *)

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". 
    (***
     Note how we use the tactic [eauto].
     ***)
   destruct c1; destruct c2; try (apply CSeq_congruence; assumption)
   ; eauto using skip_left, skip_right.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
     remember (fold_constants_bexp b) as b'.
     assert (bequiv b b').
     rewrite Heqb'.
     apply fold_constants_bexp_sound.
     destruct b'; try (apply CWhile_congruence; assumption; assumption).
     apply WHILE_true. assumption.
     assert (WHILE_false: forall b c, bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP).
     { intros. split. { intros. inversion H1. subst. apply E_Skip. subst. rewrite H0 in H4. inversion H4. }
       { intros. inversion H1. subst. apply E_WhileEnd. rewrite H0. reflexivity. } }
     apply WHILE_false.
     assumption.
Qed.

(*-- Check --*)
Check fold_constants_com_sound : 
  ctrans_sound fold_constants_com.


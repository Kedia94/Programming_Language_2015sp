Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
unfold not. intros. destruct H. destruct H; subst.
inversion H; subst. inversion H5; subst. inversion H3; subst. inversion H6; subst. rewrite H2 in H4.
inversion H4. rewrite H1 in *. clear H6. clear H4.
remember T1. induction t; try inversion H1.
rewrite H6 in *. clear H6. apply IHt1. rewrite <- Heqt. symmetry. assumption.
rewrite H4 in H3. assumption. rewrite H4 in H2. assumption. assumption.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).


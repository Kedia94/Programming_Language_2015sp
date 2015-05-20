Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
assert (WHILE_true_nonterm : forall b c st st', bequiv b BTrue -> ~( (WHILE b DO c END) / st || st' )).
{ intros. unfold not. intros. remember (WHILE b DO c END) as cw. ceval_cases (induction H0) Case; inversion Heqcw; subst; clear Heqcw.
  unfold bequiv in H. rewrite H in H0. inversion H0. apply IHceval2. reflexivity. }
  intros. split; intros.
  apply WHILE_true_nonterm in H0; [apply ex_falso_quodlibet; assumption | assumption].
  apply WHILE_true_nonterm in H0.
  apply ex_falso_quodlibet.
  assumption.
  unfold bequiv.
  simpl.
  reflexivity.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).


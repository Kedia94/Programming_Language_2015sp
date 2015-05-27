Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
intros. eapply hoare_consequence_post with (fun st => st X + st Y = n + m
  /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
apply hoare_consequence_pre with (fun st => st X + st Y = n + m).
apply hoare_while. apply hoare_seq with (fun st => st X + st Y = n + m +1 
  /\ beval st (BNot (BEq (AId X) (ANum 0))) = true).
unfold hoare_triple. intros. inversion H. unfold update; simpl. subst. unfold aeval.
inversion H0. unfold beval in H2; simpl in H2. destruct (st X). inversion H2. omega.
unfold hoare_triple. intros. inversion H0. split. inversion H; subst. unfold update. simpl.
omega.
simpl in *. inversion H; subst. simpl. unfold update; simpl. apply H2.
unfold assert_implies. intros. inversion H. omega.
unfold assert_implies. intros. inversion H; subst; simpl in *.
 apply negb_false in H1; symmetry in H1; apply beq_nat_eq in H1. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.


Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
intros. apply hoare_seq with (fun st => st X + st Y = m). eapply hoare_consequence_post. 
apply hoare_while. eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.

unfold assert_implies. intros. inversion H. simpl in *. unfold assn_sub. unfold update. simpl.
destruct (st X). inversion H1. rewrite <- H0. omega.
unfold assn_sub. unfold assert_implies. intros. simpl in *. inversion H.
apply negb_false in H1. symmetry in H1. apply beq_nat_eq in H1. rewrite H1 in H0. apply H0.
unfold hoare_triple. intros. inversion H; subst. unfold update. simpl. omega.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  

Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
intros.
apply hoare_consequence_post with (fun st => fact (st X) * st Y = fact m 
                                              /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
eapply hoare_seq. apply hoare_while.
unfold hoare_triple; intros. inversion H0. inversion H; subst. rewrite <- H1.
inversion H5; subst. inversion H8; subst. unfold update; simpl.
 unfold beval in H2. simpl in H2. destruct (st X). inversion H2.
replace (S n -1) with n by omega. rewrite mult_comm with (st Y) (S n). rewrite mult_assoc. 
replace (fact n * S n) with (fact (S n)). omega.
simpl. rewrite mult_comm. replace (S n) with (n + 1) by omega. rewrite mult_plus_distr_l. omega.
unfold hoare_triple. intros. inversion H; subst. unfold update; simpl. omega.
unfold assert_implies. intros. inversion H. unfold beval in H1. simpl in H1. apply negb_false in H1.
symmetry in H1. apply beq_nat_eq in H1. rewrite H1 in H0. simpl in H0. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.


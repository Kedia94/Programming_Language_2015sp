Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
intros.
eapply hoare_seq with (fun st => st X = 0).
eapply hoare_seq with (fun st => st X = 0 /\ st Y = 0).
eapply hoare_seq with (fun st => st X = 0 /\ st Y = 0 /\ st Z = c).
eapply hoare_seq with (fun st => st X = a /\ st Y = 0 /\ st Z = a+c).
eapply hoare_consequence_post with (fun st => (st Z = st Y + a+c) /\ beval st (BNot (BEq (AId Y) (ANum b))) = false).
eapply hoare_consequence_pre with (fun st => (st Z = st Y + a+c)).
apply hoare_while.
unfold hoare_triple. intros. inversion H0. inversion H; subst. inversion H5; subst. inversion H8; subst. unfold update;simpl. omega.
unfold assert_implies. intros. omega.
unfold assert_implies. intros. simpl in H. inversion H. apply negb_false in H1. symmetry in H1; apply beq_nat_eq in H1. omega.
eapply hoare_consequence_post with (fun st => ((st Z = st X + c /\ st Y = 0) /\ beval st (BNot (BEq (AId X) (ANum a))) = false)).
eapply hoare_consequence_pre with (fun st => (st Z = st X + c /\ st Y = 0)).
apply hoare_while.
unfold hoare_triple. intros. inversion H; subst. inversion H3; inversion H6; subst. unfold update; simpl. inversion H0. omega.
unfold assert_implies. intros. omega.
unfold assert_implies. intros. inversion H. simpl in H1. apply negb_false in H1. symmetry in H1; apply beq_nat_eq in H1. omega.
unfold hoare_triple. intros. inversion H; subst. unfold update; simpl. inversion H0. split. apply H1. split. apply H2. reflexivity.
unfold hoare_triple. intros. inversion H; subst. unfold update; simpl. split. assumption. reflexivity.
unfold hoare_triple. intros. inversion H; subst. unfold update; simpl. reflexivity.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.


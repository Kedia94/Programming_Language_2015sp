Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
unfold hoare_triple. intros.
inversion H; subst. unfold beval in H6. simpl in H6.
inversion H7; subst. unfold update; simpl.
generalize dependent (st X) . generalize dependent (st Y).
induction n. intros. destruct n. reflexivity. inversion H6.
destruct   n0. intros; omega. simpl. intros. apply f_equal. apply IHn. apply H6.
unfold beval in H6; simpl in H6. inversion H7; subst. unfold update; simpl. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 


Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
match t with
  | ttrue  => match T with TBool => true | TNat => false end
  | tfalse => match T with TBool => true | TNat => false end
  | tif a b c => andb (andb (tycheck a TBool) (tycheck b T)) (tycheck c T)
  | tzero  => match T with TBool => false | TNat => true end
  | tsucc a  => andb (tycheck a TNat) (match T with TBool => false | TNat => true end)
  | tpred a  => andb (tycheck a TNat) (match T with TBool => false | TNat => true end)
  | tiszero a => andb (tycheck a TNat) (match T with TBool => true | TNat => false end)
end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. simpl. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. simpl. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
induction t.
  destruct T; intros. constructor. inversion TYCHK.
  destruct T; intros. constructor. inversion TYCHK.
  destruct T; intros; simpl in TYCHK; apply andb_true_iff in TYCHK as [I1 I3]; apply andb_true_iff in I1 as [I1 I2].
    constructor. apply IHt1; apply I1. apply IHt2; apply I2. apply IHt3; apply I3.
    constructor. apply IHt1; apply I1. apply IHt2; apply I2. apply IHt3; apply I3.
  destruct T; intros. inversion TYCHK. constructor.
  destruct T; intros. simpl in TYCHK. apply andb_true_iff in TYCHK as [K J]; inversion J. constructor; apply IHt; apply andb_true_iff in TYCHK as [K J]; apply K.
  destruct T; intros; simpl in TYCHK; apply andb_true_iff in TYCHK as [K J]. inversion J. constructor; apply IHt; apply K.
  destruct T; intros; simpl in TYCHK; apply andb_true_iff in TYCHK as [K J]. constructor; apply IHt; apply K. inversion J.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
induction t.
  destruct T; intros. constructor. inversion HASTY.
  destruct T; intros. constructor. inversion HASTY.
  destruct T; intros; inversion HASTY; subst. simpl. apply andb_true_iff; split. apply andb_true_iff; split.
    apply IHt1; apply H2. apply IHt2; apply H4. apply IHt3; apply H5.
    simpl. apply andb_true_iff; split. apply andb_true_iff; split. apply IHt1; apply H2. apply IHt2; apply H4. apply IHt3; apply H5.
  destruct T; intros. inversion HASTY. constructor.
  destruct T; intros. inversion HASTY. simpl. apply andb_true_iff. split. apply IHt. inversion HASTY. apply H0. reflexivity.
  destruct T; intros. inversion HASTY. simpl; apply andb_true_iff; split. apply IHt. inversion HASTY; apply H0. reflexivity.
  destruct T; intros. inversion HASTY. simpl; apply andb_true_iff; split. apply IHt. apply H0. reflexivity. inversion HASTY.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.

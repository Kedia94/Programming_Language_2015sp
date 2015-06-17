Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  tfix
    (tabs Halve (TArrow TNat TNat)
      (tabs X TNat
        (tif0
          (tvar X)
          (tnat 0)
          (tif0
            (tpred (tvar X))
            (tnat 0)
            (tsucc (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
unfold halve; eauto 10.
  (* unfold halve; eauto 10. *)
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
unfold halve; normalize.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
intros. induction n. unfold halve. normalize.
eapply multi_step. apply ST_AppFix. constructor. constructor.
eapply multi_step. apply ST_App1. apply ST_AppAbs. constructor. constructor. simpl.
eapply multi_step. apply ST_AppAbs. constructor. simpl. 
eapply multi_step. apply ST_If0Nonzero.
eapply multi_step. apply ST_If01. apply ST_PredNat. simpl. rewrite <- plus_comm. simpl.
eapply multi_step. apply ST_If0Nonzero.
eapply multi_step. apply ST_Succ1. apply ST_App2. constructor. constructor. apply ST_Pred. apply ST_PredNat.
eapply multi_step. apply ST_Succ1. apply ST_App2. constructor. constructor. apply ST_PredNat. simpl.
inversion IHn. subst.
eapply multi_step. apply ST_Succ1. apply H.
apply multi_trans with (y:= tsucc (tnat n)).
assert (forall a b, (multi step a b) -> (multi step (tsucc a) (tsucc b))).
{ intros. induction H1. constructor. eapply multi_step. constructor. apply H1. apply IHmulti. }
apply H1. apply H0.
apply multi_step with (y0:= (tnat (S n))). constructor. constructor.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.


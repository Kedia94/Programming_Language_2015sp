Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
intros. induction b.
left. left. reflexivity.
left. right. reflexivity.
{ remember (aexp_strong_progress st a). inversion o. inversion H. remember (aexp_strong_progress st a0). inversion o0. inversion H1. subst. right. exists (if (beq_nat x x0) then BTrue else BFalse). constructor.
  inversion H1. right. exists (BEq a x0). constructor. subst. constructor. apply H2.
  right. inversion H. exists (BEq x a0). constructor. apply H0. }
{ remember (aexp_strong_progress st a). inversion o. inversion H. remember (aexp_strong_progress st a0). inversion o0. inversion H1. subst. right. exists (if (ble_nat x x0) then BTrue else BFalse). constructor.
  inversion H1. right. exists (BLe a x0). constructor. rewrite H0. constructor. apply H2.
  right. inversion H. exists (BLe x a0). constructor. apply H0. }
inversion IHb. inversion H. subst. right. exists BFalse. constructor. subst; right. exists BTrue. constructor.
  inversion H; subst. right. exists (BNot x). constructor. apply H0.
inversion IHb1. inversion IHb2. inversion H; inversion H0; subst.
  right. exists BTrue. constructor. right. exists (BFalse). constructor. right. exists BFalse. constructor. right. exists BFalse. constructor.
  inversion H0; subst. inversion H; subst. right. exists (BAnd BTrue x). constructor. apply H1.
  right. exists BFalse. constructor.
  inversion H. right. exists (BAnd x b2). constructor. apply H0. 
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.


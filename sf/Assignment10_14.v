Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
intros. induction a. left. exists n. reflexivity.
right. exists (ANum (st i)). apply AS_Id.
right. destruct IHa1; destruct IHa2. inversion H; inversion H0. subst. exists (ANum (x+x0)). constructor.
inversion H; subst. inversion H0. exists (APlus (ANum x) x0). constructor. trivial. apply H1.
  inversion H0; subst. inversion H. exists (APlus x0 (ANum x)). constructor. apply H1.
  inversion H; inversion H0.  exists (APlus x a2). constructor. apply H1. 
right. destruct IHa1. destruct IHa2. inversion H. inversion H0. subst. exists (ANum (x-x0)). constructor.
  inversion H; inversion H0; subst. exists (AMinus (ANum x) x0). constructor. trivial. apply H2.
  inversion H. exists (AMinus x a2). constructor. apply H0.
right. destruct IHa1. destruct IHa2. inversion H; inversion H0; subst. exists (ANum (mult x x0)). constructor.
  inversion H. inversion H0. subst. exists (AMult (ANum x) x0). constructor. trivial. apply H2.
  inversion H; subst. exists (AMult x a2). constructor. apply H0.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.


Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
intros. induction c.
left. reflexivity.
{ remember (aexp_strong_progress st a). inversion o. inversion H. subst. right. exists SKIP. exists (update st i x). constructor.
  inversion H. right. exists (i ::= x). exists st. constructor. assumption. }
inversion IHc1. subst. right. exists c2. exists st. constructor.
  inversion H. right. exists (x ;; c2). inversion H0. exists x0. constructor. apply H1.
remember (bexp_strong_progress st b). inversion o. inversion H. right. subst. exists c1. exists st. constructor. subst. right. exists c2. exists st. constructor.
  inversion H. right. exists (IFB x THEN c1 ELSE c2 FI). exists st. constructor. apply H0.
right. exists (IFB b THEN (c;; (WHILE b DO c END)) ELSE SKIP FI). exists st. constructor.
inversion IHc1; subst; right. inversion IHc2; subst. exists SKIP. exists st. constructor.
  inversion H. inversion H0. exists (PAR SKIP WITH x END). exists x0. constructor. apply H1.
  inversion H. inversion H0. exists (PAR x WITH c2 END). exists x0. constructor. apply H1.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.


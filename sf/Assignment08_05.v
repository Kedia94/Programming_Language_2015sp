Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
 | ANum v => [SPush v]
 | AId i => [SLoad i]
 | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
 | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
 | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
assert (K: forall (e : aexp) (st : state) (s1 : list nat) (other : list sinstr),
    s_execute st s1 (s_compile e ++ other) =
    s_execute st ((aeval st e) :: s1) other).
{induction e; try reflexivity. simpl. intros. assert ((s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ other = s_compile e1 ++ s_compile e2 ++ [SPlus] ++ other). rewrite app_ass. rewrite app_ass. reflexivity.
  rewrite H. assert (s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SPlus :: other) = s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other)). apply IHe1. simpl. rewrite H0.
  assert (s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other) = s_execute st (aeval st e2 :: aeval st e1 :: s1) (SPlus :: other)). apply IHe2. rewrite H1. simpl. reflexivity.
intros. assert (s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SMinus :: other) = s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other)). apply IHe1. assert ((s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ other = s_compile e1 ++ s_compile e2 ++ [SMinus] ++ other). rewrite app_ass. rewrite app_ass. reflexivity.
simpl. rewrite H0. simpl. rewrite H. assert (s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other) = s_execute st (aeval st e2 :: aeval st e1 :: s1) (SMinus :: other)). apply IHe2. rewrite H1. simpl. reflexivity.
  intros. assert ((s_compile e1 ++ s_compile e2 ++ [SMult]) ++ other = s_compile e1 ++ s_compile e2 ++ [SMult] ++ other). rewrite app_ass. rewrite app_ass. reflexivity.
assert (s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SMult :: other) = s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other)). apply IHe1. assert (s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other) = s_execute st (aeval st e2 :: aeval st e1 :: s1) (SMult :: other)).
apply IHe2.  simpl. rewrite H. simpl. rewrite H0. simpl. rewrite H1. simpl. reflexivity. }
intros. replace ([aeval st e]) with (s_execute st [aeval st e] []). replace (s_compile e) with (s_compile e++[]). apply K. 
rewrite app_nil_end. reflexivity. reflexivity.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].


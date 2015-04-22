Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
intros. induction l1. simpl. reflexivity. simpl. rewrite IHl1. reflexivity.
  (* FILL IN HERE *)
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
intros. induction H. exists []. exists l. simpl. reflexivity.
destruct IHappears_in. exists (b::witness). simpl. destruct proof. exists witness0. rewrite proof. reflexivity.
  (* FILL IN HERE *)
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
    re_here  : forall (x : X) (l : list X), appears_in x l -> repeats (x :: l)
  | re_next : forall (x : X) (l : list X), repeats l -> repeats (x :: l).
  (* FILL IN HERE *)


(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
intros X l1. induction l1 as [|x l1'].
 { intros. inversion H1. }
 { intros. simpl in H1. remember (H (appears_in x l1')) as ai_x_l1. destruct ai_x_l1. apply re_here. apply a.
   apply re_next. remember (appears_in_app_split X x l2 (H0 x (ai_here x l1'))). destruct e as [w1 [w2]]. apply IHl1' with (l2:= (w1++w2)). apply H.
   intros. assert (H2' := H2). apply ai_later with (b:=x) in H2'. apply H0 in H2'. rewrite proof in H2'. apply appears_in_app in H2'. destruct H2'.
   apply app_appears_in. left. apply H3. apply app_appears_in. right. inversion H3. rewrite H5 in H2.
   unfold not in n. apply n in H2. inversion H2. apply H5.
   rewrite proof in H1. rewrite app_length in H1. simpl in H1.
      assert (K: forall (a b: nat), a + S b = S (a + b)). { intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity. }
   rewrite K in H1. SearchAbout le. apply Sn_le_Sm__n_le_m in H1. rewrite <- app_length in H1. apply H1. }
Qed.
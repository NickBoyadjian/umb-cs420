(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Turing.Util.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---------------------------------------------------------------------------*)


(**

Study the definition of [Turing.Util.pow] and [Turing.Util.pow1]
and then show that [Turing.Util.pow1] can be formulated in terms of
[Turing.Util.pow].
Material: https://gitlab.com/cogumbreiro/turing/blob/master/src/Util.v


 *)
Theorem ex1: forall (A:Type) (x:A) n, Util.pow [x] n = Util.pow1 x n.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(**

Study recursive definition of [List.In] and the inductive definition of
[List.Exists]. Then show that [List.In] can be formulated in terms
of [List.Exists].

Material: https://coq.inria.fr/library/Coq.Lists.List.html


 *)
Theorem ex2: forall (A:Type) (x:A) l, List.Exists (eq x) l <-> List.In x l.
Proof.
  intros.
  induction l.
  - simpl.
    apply Exists_nil.
  - simpl.
    rewrite <- IHl.
    rewrite Exists_cons.
    rewrite IHl.
    rewrite or_comm.
    symmetry.
    split.
    * intros.
      inversion H.
      { right. rewrite <- H0. reflexivity. }
      { left. apply H0. }
    * intuition.
Qed.

(**

Create an inductive relation that shows that the list on the left
is a prefix of the list on the right; or, to put it differently,
the second list starts with the first list.

Exercise [ex3] should guide you on figuring out which cases your require.


 *)

Inductive Prefix {A:Type}: list A -> list A -> Prop := 
  | prefix_nill : forall l , Prefix [] l
  | prefix_add_one : forall (x : A) (l1 : list A) (l2 : list A), 
      Prefix l1 l2 -> Prefix (x :: l1) (x :: l2).


Theorem prefix1: Prefix [1;2;3] [1;2;3;4].
Proof.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_nill.
Qed.


Theorem prefix2: Prefix [1;2;3] [1;2;3].
Proof.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_nill.
Qed.


Theorem prefix3: Prefix [1;2;3] [1;2;3;4;5;6].
Proof.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_add_one.
  apply prefix_nill.
Qed.


Theorem prefix4: forall (l:list nat), Prefix [] l.
Proof.
  intros.
  apply prefix_nill.
Qed.


(**

The proof should follow *without* requiring induction to conclude.
The conclusion of this proof should guide you on figuring out what
constructors to write for Prefix.
 *)


Theorem ex3: forall A l1 l2, @Prefix A l1 l2 -> l1 = [] \/ (exists x l1' l2', l1 = x :: l1' /\ l2 = x :: l2' /\ Prefix l1' l2').
Proof.
  intros.
  destruct H.
  - intros. left. auto.
  - right.
    -- exists x, l1, l2.
      * split. 
        { reflexivity. }
        ** split. { reflexivity. } { apply H. }
Qed.

Theorem ex4: forall A l1 l2, @Prefix A l1 l2 -> exists l3, l2 = l1 ++ l3.
Proof.
  intros.
  induction H.
  - exists l. auto.
  - destruct IHPrefix. subst. exists x0. simpl. reflexivity.
Qed.

(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Turing.Lang.
Require Import Turing.Regular.
Require Import Turing.Regex.
Require Import Turing.Util.
Require Import Omega.
Import ListNotations.
Import RegexNotations.
Import Lang.LangNotations.
Open Scope char_scope.
Open Scope lang_scope.
Open Scope regex_scope.

(* ---------------------- END OF PREAMBLE ------------------ *)

(**

  The objective of this homework assignment is to prove that
  language L5 is not regular, where L5 is a^n b^m where n < m.


  WARNING: DO NOT CHANGE DEFINITION L5, otherwise you will get 0 points for
  this assignment.

*)
Definition L5 : language := fun w => exists n m, w = pow1 "a" n ++ (pow1 "b" ((S m) + n)).
Lemma pow1_app_cons_inv_eq_1:
forall {T} (a b:T),
a <> b ->
forall x y v w,
pow1 a x ++ b :: y = pow1 a v ++ b :: w ->
x = v.
Proof.
intros ? a b.
induction x; intros. {
    simpl in *.
    destruct v; auto.
    simpl in *.
    inversion H0.
    subst.
    contradiction.
}
simpl in *.
destruct v; simpl in *. {
    inversion H0.
    subst.
    contradiction.
}
inversion H0; subst; clear H0.
apply IHx in H2.
subst; reflexivity.
Qed.


(* ---------------------------------------------------------------------------*)


(**

Easy. Show that the word that clogs is in L5.

 *)
Theorem l5_not_regular_1: forall p, In (pow1 "a" p ++ pow1 "b" (S p)) L5.
Proof.
  intros.
  unfold In, L5.
  exists p, 0.
  simpl.
  reflexivity.
Qed.

(**

Easy. Show that the clogged word has at least p-characters.

 *)
Theorem l5_not_regular_2: forall p, length (pow1 "a" p ++ pow1 "b" (S p)) >= p.
Proof.
  intros.
  rewrite app_length.
  rewrite pow1_length.
  omega.
Qed.

(**

Difficult. The proof for Regular.Examples.l4_not_regular_alt is similar to what you should be doing. 
The only theorem you need to use is Regular.Examples.xyz_rw_ex.


 *)


Theorem l5_not_regular_4_1: forall p x y z n m, p >= 1 -> y <> [] -> pow1 "a" p ++ "b" :: pow1 "b" p = x ++ y ++ z -> length (x ++ y) <= p -> x ++ (y ++ y) ++ z = pow1 "a" n ++ pow1 "b" (S m + n) -> exists nx ny o,
    ny <> 0 /\
    pow1 "a" nx ++
    (pow1 "a" ny ++ pow1 "a" ny) ++
    pow1 "a" o ++
    "b" :: pow1 "b" (length (pow1 "a" nx ++ pow1 "a" ny) + o)
    =
    pow1 "a" n ++ pow1 "b" (S m + n).
Proof.
 intros.
  apply Regular.Examples.xyz_rw_ex in H1; auto.
  - destruct H1 as (b, (H4, (H5, (H6, (H7, H8))))).
    clear H2.
    rename H3 into N.
    rewrite H4 in H8; clear H4.
    rewrite H6 in N; clear H6.
    rewrite H7 in N; clear H7.
    rewrite H8 in N; clear H8.
    repeat rewrite app_assoc in *.
    repeat rewrite pow1_plus in *.
    exists (length x), (length y), b.
    split.
    * intros M. destruct y. 
      { contradiction H0. reflexivity. }
      { inversion M. }
    * repeat rewrite app_assoc in *.
      repeat rewrite pow1_plus in *.
      Search (length (pow1 _ _)).
      rewrite pow1_length.
      rewrite app_length in N.
      rewrite <- N. simpl. reflexivity.
Qed.

(**

Easy. Use rewriting rules (eg, app_assoc).

 *)
Theorem l5_not_regular_4_2: forall nx ny n m o, pow1 "a" nx ++ (pow1 "a" ny ++ pow1 "a" ny) ++ pow1 "a" o ++ "b" :: pow1 "b" (length (pow1 "a" nx ++ pow1 "a" ny) + o) = pow1 "a" n ++ pow1 "b" (S m + n) -> pow1 "a" (nx + ny + ny + o) ++ "b" :: pow1 "b" (nx + ny + o) = pow1 "a" n ++ "b" :: pow1 "b" (m + n).
Proof.
  intros.
  repeat rewrite app_assoc in H.
  repeat rewrite pow1_plus in H.
  repeat rewrite pow1_length in H.
  simpl in *.
  apply H.
Qed.

(**

Hard. This is the final step of the proof. You want to start by showing that the powers of "a" are equal 
(for which you'll need pow1_app_cons_inv_eq_1). After that you want to remove the left-hand side of the 
equality with app_inv_head. Your final step should be to conclude that both powers must be equal. 
Once you have an equality over naturals, then use `omega` to conclude.

  intros.
  repeat rewrite <- pow1_append. 
  intros N.
  apply pow1_a_b_inv_eq in N.
  - destruct N as (L, R). 
    symmetry in R.
    subst.
    rewrite <- plus_assoc in R.
    rewrite plus_comm in R.
    repeat rewrite <- plus_assoc in R.
    apply plus_inv_eq_r in R.
    rewrite plus_comm in R. 
    repeat rewrite <- plus_assoc in R.
    repeat apply plus_inv_eq_r in R.
    apply plus_is_O in R. 
    destruct R as (L, R).
    omega.
  - intro. inversion H0.


 *)

Theorem pow1_append: forall (x:nat) (w:ascii), pow1 w (x + 1) = w :: pow1 w x.
Proof.
  intros. induction x. Search (pow1 _ (_ + 1)).
  - reflexivity.
  - simpl. rewrite IHx. auto.
Qed.

Theorem l5_not_regular_4_3: forall nx ny o n m, ny <> 0 -> pow1 "a" (nx + ny + ny + o) ++ "b" :: pow1 "b" (nx + ny + o) <>
    pow1 "a" n ++ "b" :: pow1 "b" (m + n).
Proof. 
  intros.
  repeat rewrite <- pow1_append. 
  intros N.
  apply pow1_a_b_inv_eq in N.
  - destruct N as (L, R). 
    symmetry in R.
    subst.
    rewrite <- plus_assoc in R.
    rewrite plus_comm in R.
    repeat rewrite <- plus_assoc in R.
    apply plus_inv_eq_r in R.
    rewrite plus_comm in R. 
    repeat rewrite <- plus_assoc in R.
    repeat apply plus_inv_eq_r in R.
    apply plus_is_O in R. 
    destruct R as (L, R).
    omega.
  - intro. inversion H0.
Qed.

(**

Easy. Use the lemmas that start with l5_not_regular_4_

  intros.
  intros N.
  assert(Hx:=l5_not_regular_4_1 p x y z n m H H0 H1 H2 N).
  destruct Hx as (nx, (ny, (o, (H3, Hx)))).
  assert(Hy:=l5_not_regular_4_2 nx ny n m o).
  assert(Hz:=l5_not_regular_4_3 nx ny o n m H3).
  destruct Hz.
  apply Hy. apply Hx.

 *)
Theorem l5_not_regular_4: forall p m n x y z, p >= 1 -> y <> [] -> 
pow1 "a" p ++ "b" :: pow1 "b" p = 
x ++ y ++ z -> length (x ++ y) <= p -> x ++ (y ++ y) ++ z <> pow1 "a" n ++ pow1 "b" (S m + n).
Proof.
  intros; intros N.
  assert(M:=l5_not_regular_4_1 p x y z n m H H0 H1 H2 N).
  destruct M as (x0, (x1, (x2, (H3, H4)))).
  assert(Hx:=l5_not_regular_4_2 x0 x1 n m x2).
  assert(Hz:=l5_not_regular_4_3 x0 x1 x2 n m H3).
  destruct Hz.
  apply Hx, H4.
Qed.

(**

Easy. Show that a^p b^(p+1) clogs L5. Conclude the proof using Lemma l5_not_regular_4 to conclude.


 *)


Theorem l5_not_regular_3: forall p, p >= 1 -> In (pow1 "a" p ++ pow1 "b" (S p)) (Clogs L5 p).
Proof.
  intros.
  unfold In, Clogs.
  intros.
  exists 2.
  intros N.
  unfold In, L5 in N.
  destruct N as (a, (b, N')).
  simpl in *.
  rewrite app_nil_r in N'.
  apply l5_not_regular_4 with (p:=p) in N'.
  - assumption. - apply H. - apply H1. - apply H0. - apply H2.
Qed.

(**

Easy. Show that L5 is not regular.

 *)
Theorem l5_not_regular: ~ Regular L5.
Proof.
  unfold L5.
  apply not_regular.
  intros.
  apply clogged_def with (w:=(pow1 "a" p ++ pow1 "b" (1 + p)) % list).
  - apply l5_not_regular_1.
  - apply l5_not_regular_2.
  - apply l5_not_regular_3.
    * apply H.
Qed.


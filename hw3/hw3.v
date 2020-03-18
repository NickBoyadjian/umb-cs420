(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.


(* ---------------------------------------------------------------------------*)


(**

Show that any word that is in L4 is either empty or starts with "a".

 *)


Theorem ex1: forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof.
  intros.
  induction H.
  induction x.
  - left. 
    destruct H as (x, (x0, (H, (H0, H1)))).
    inversion H0; inversion H1.
    rewrite H. rewrite <- H3. rewrite <- H4.  reflexivity.
  - right.
    destruct H as (x0, (x1, (H, (H0, H1)))).
    inversion H0; inversion H1. 
    exists (w2 ++ w0 ++ w4).
    unfold Char in H4.
    rewrite H, H10, H5, H4. reflexivity.
Qed.


(**

Show that the following word is accepted by the given language.

 *)

Lemma b_in_b:
  Char "b" ["b"].
Proof.
  unfold Char.
  reflexivity.
Qed.

Lemma in_bb:
  In ["b"; "b"] (Pow (Char "b") 2).
Proof.
  unfold In.
  (* { a } *)
  apply pow_cons with (w1:=["b"]) (w2:=["b"]).
  - apply pow_cons with (w1:=["b"]) (w2:=[]).
      * apply pow_nil.
      * apply b_in_b.
      * reflexivity.
  - apply b_in_b.
  - reflexivity.
Qed.

Theorem ex2: In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  unfold Star.
  unfold In.
  unfold App.
  exists ["a"; "b"; "b"], ["a"].
  split.
  - simpl. reflexivity.
  - split.
    -- exists ["a"], ["b";"b"]. split.
       { reflexivity. }
       { split. - reflexivity. - exists 2. apply in_bb. }
    -- reflexivity.
Qed.


(**

Show that the following word is rejected by the given language.

 *)


Theorem ex3: ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  unfold not.
  intros.
  unfold In, App in H.
  destruct H as (w1, (w2, H)).
  destruct H as (Ha, (Hb, Hc)).
  destruct Hb as (Hd, (He, Hf)).
  destruct Hf.
  destruct H0.
  unfold Char in H0.
  subst.
  inversion Ha.
Qed.

(**

Show that the following language is empty.

 *)
Theorem ex4: "0" * >> {} == {}.
Proof.
  apply app_r_void_rw.
Qed.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)


Theorem ex5: ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  unfold Equiv.
  split.
  - intros. 
    rewrite <- app_union_distr_l in H.
    rewrite app_l_nil_rw in H.
    apply H.
  - intros.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    apply H.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6: ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  unfold Equiv.
  split; intros.
  - unfold Union, In, App in *.
    destruct H. destruct H as (x, (x0, H)). 
    left.
    -- destruct H. rewrite H. inversion H0. 
       unfold Char in *. rewrite H1. rewrite H2. reflexivity.
    -- right. destruct H as (x, (x0, (H, (H0, H1)))).
       unfold Char in *.
       rewrite H, H0, H1.
       reflexivity.
  - unfold In, Union, App in *. destruct H.
    -- left. exists ["0"], ["1"]. split.
       * rewrite H. reflexivity.  
       * split. 
          ** unfold Char; reflexivity. 
          ** unfold Char; reflexivity.
    -- unfold In, Union, App. right. exists ["1"], ["0"]. split.
       * rewrite H. reflexivity. 
       * split. 
         ** unfold Char; reflexivity. 
         ** unfold Char; reflexivity.
Qed.

Theorem ex7: "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  split; intros.
  - rewrite app_r_nil_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    rewrite union_sym_rw.
    apply H.
  - rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw in H.
    apply H.
Qed.


Theorem ex8: (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  split; intros.
  - rewrite union_r_void_rw in H.
    rewrite app_r_void_rw in H.
    rewrite app_l_void_rw in H.
    rewrite star_void_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    apply H.
  - rewrite union_r_void_rw.
    rewrite app_r_void_rw.
    rewrite app_l_void_rw.
    rewrite star_void_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    apply H.
Qed.


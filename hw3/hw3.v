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
  unfold L4 in H.
  induction H.
  destruct x.
  - left. apply pow_pow_in_inv in H. simpl in *. rewrite H. reflexivity.
  - right. apply pow_pow_in_inv in H.
    subst. simpl. exists ["a";"b"].  
Admitted.


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
  unfold In.
  unfold App.
  unfold Star.
  unfold pow.
  intros.
  
Admitted.

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
Admitted.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6: ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  
Admitted.


Theorem ex7: "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
Admitted.


Theorem ex8: (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
Admitted.


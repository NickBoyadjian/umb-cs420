(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.
Require Import Hw5Util.

(* ---------------------------------------------------------------------------*)


(**

Use `yield_def`.

 *)
Theorem yield_eq: forall G A w, List.In (A, w) (Hw5Util.grammar_rules G) -> Hw5Util.Yield G [A] w.
Proof.
  intros.
  apply yield_def with (u:=[]) (v:=[]) (w:=w) (A:=A).
  - apply H.
  - reflexivity.
  - apply app_nil_end.
Qed.

(**

Use `yield_def` and `app_assoc` to correct the parenthesis.

 *)
Theorem yield_right: forall G w1 w2 r w3 w4, Hw5Util.Yield G w1 w2 -> w3 = w1 ++ r -> w4 = w2 ++ r -> Hw5Util.Yield G w3 w4.
Proof.
Admitted.

(**

Similar proof than `yield_right`, but you should rewrite with
`app_assoc` after using `yield_def`, not before.


 *)
Theorem yield_left: forall G w1 w2 l w3 w4, Hw5Util.Yield G w1 w2 -> w3 = l ++ w1 -> w4 = l ++ w2 -> Hw5Util.Yield G w3 w4.
Proof.
Admitted.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_1: Hw5Util.Yield g1 ["C"] ["{"; "C"; "}"].
Proof.
Admitted.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_2: Hw5Util.Yield g1 ["C"] ["C"; "C"].
Proof.
Admitted.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_3: Hw5Util.Yield g1 ["C"] [].
Proof.
Admitted.

(**

The proof should proceed by inversion and then case analysis on
string `u`.


 *)
Theorem yield_inv_start: forall G w, Hw5Util.Yield G [Hw5Util.grammar_start G] w -> In (Hw5Util.grammar_start G, w) (Hw5Util.grammar_rules G).
Proof.
Admitted.

(**

You will want to use `yield_inv_start`. Recall that that `List.In`
simplifies to a series of disjunctions.


 *)
Theorem g1_ex1: ~ Hw5Util.Yield g1 ["C"] ["{"].
Proof.
Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_1: Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.
Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_2: Hw5Util.Yield g1 ["{"; "C"; "}"; "C"] ["{"; "}"; "C"].
Proof.
Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_3: Hw5Util.Yield g1 ["{"; "}"; "C"] ["{"; "}"; "{"; "C"; "}"].
Proof.
Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_4: Hw5Util.Yield g1 ["{"; "}"; "{"; "C"; "}"] ["{"; "}"; "{"; "}"].
Proof.
Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_1: Hw5Util.Derivation g1 [["C"]].
Proof.
Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_2: Hw5Util.Derivation g1 [["C"; "C"]; ["C"]].
Proof.
Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_3: Hw5Util.Derivation g1 [["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
Proof.
Admitted.


Theorem g1_der_4: Hw5Util.Derivation g1 [
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
Admitted.


Theorem g1_der_5: Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
Admitted.


Theorem g1_der_6: Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "}"];
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
Admitted.

(**

Use `g1_der_6`.

 *)
Theorem ex1: Accept g1 ["{"; "}"; "{"; "}"].
Proof.
Admitted.


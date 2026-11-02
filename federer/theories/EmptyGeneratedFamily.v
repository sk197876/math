(** Federer (1969), 2.2.1, p. 60, empty-generator correction in erratum p.
    1, book p. 60 line 4. The local counterexample below explains why the
    missing hypothesis matters; it is not a counterexample printed in
    Federer. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP BorelFamilyBasic CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [empty_only_countably_closed]: Federer 2.2.1, p. 60,
    supporting empty case for the weaker closure classes *)
Lemma empty_only_countably_closed (d : bool) (I : choiceType) (X : set I) :
  is_countably_closed_family d X [set A | A = set0].
Proof.
constructor.
- by [].
- by move=> A -> x [].
- move=> G hG _ _; apply/seteqP; split=> [x [A hA hx]|x []].
  by rewrite (hG A hA) in hx.
- move=> G hG _ [A hA]; apply/seteqP; split=> [x hx|x []].
  have h := hx A hA; by rewrite (hG A hA) in h.
Qed.

(** Source for [empty_generators_closed_specification]: Federer
    2.2.1, p. 60, local boundary case supporting the erratum:
    generating either weaker closure class from no generators
    yields exactly the family containing only the empty set. *)
Lemma empty_generators_closed_specification (d : bool) (I : choiceType) (X : set I) :
  is_generated_closed_family d X set0 [set A | A = set0].
Proof.
constructor.
- exact: empty_only_countably_closed.
- by move=> A [].
- move=> F hF _ A ->; exact: countably_closed_family_empty hF.
Qed.

(** Source for [empty_only_not_borel]: local counterexample
    explaining Federer's erratum p. 1, book p. 60 line 4,
    for 2.2.1. On a nonempty space, the family containing only
    the empty set lacks its relative complement X and is not Borel. *)
Lemma empty_only_not_borel (I : choiceType) (X : set I) :
  (exists x, X x) -> ~ is_borel_family X [set A | A = set0].
Proof.
move=> [x hx] hF; have he := borel_family_whole hF.
change (X = set0) in he; by rewrite he in hx.
Qed.

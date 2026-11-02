(** Federer (1969), 3.2.18, p. 255:
    assemble disjoint positive compact chart
    images. This supporting finite-measure argument
    uses the previously proved opaque maximal
    disjoint-family laws and numerical-sum countability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure
  MeasureDisjointSupport CountablyClosedFamilyUP MaximalDisjointFamily
  MaximalDisjointFamilyUP MaximalDisjointFamilyInsertion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_maximal_positive_cover]:
    a disjoint countable family with null
    remainder, supporting Federer 3.2.18,
    p. 255. Its supply premise is
    discharged by the separate positive-chart
    theorem, rather than assumed in the
    final rectifiability lemma. *)
Theorem finite_measure_maximal_positive_cover (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (W : set X) (P : set (set X)) :
  is_measure mu -> measure_measurable mu W -> mu W< +oo ->
  (forall C, P C -> C `<=` W /\ measure_measurable mu C /\ 0<mu C) ->
  (forall A, measure_measurable mu A -> A `<=` W -> 0<mu A ->
    exists C, P C /\ C `<=` A) ->
  exists G : set (set X), countable G /\ G `<=` P /\ set_family_disjoint G /\
    mu (W `\` (\bigcup_(C in G) C))=0.
Proof.
move=> hm hW hFin hEligible hSupply.
pose G := maximal_disjoint_family P.
have hG := maximal_disjoint_family_specification P.
have hMember C (hC : G C) : P C := maximal_disjoint_family_members hG hC.
have hSub C (hC : G C) : C `<=` W := (hEligible C (hMember C hC)).1.
have hMeas C (hC : G C) : measure_measurable mu C := (hEligible C (hMember C hC)).2.1.
have hPos C (hC : G C) : 0<mu C := (hEligible C (hMember C hC)).2.2.
have hDis : set_family_disjoint G := maximal_disjoint_family_disjoint hG.
have hCount0 := @measure_disjoint_positive_countable R X [the choiceType of set X]
  mu hm W G (fun C=>C) hFin hSub hMeas hDis.
have hEq : G `&` [set C | 0<mu C]=G.
  apply/seteqP; split=> C; [by move=> []|move=> hC; split=> //; exact: hPos C hC].
rewrite hEq in hCount0.
pose U := \bigcup_(C in G) C.
have hU : measure_measurable mu U.
  exact: (@measure_measurable_countable_union R X [the choiceType of set X]
    mu hm G (fun C=>C) hCount0 hMeas).
have hR := measure_measurable_difference hm hW hU.
have hZero : mu (W `\` U)=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
  apply/negP=> hpositive.
  have hRW : W `\` U `<=` W by move=> x hx; exact hx.1.
  have [C [hC hCR]] := hSupply _ hR hRW hpositive.
  have hNewEmpty : C=set0.
    apply: (maximal_disjoint_family_no_new_piece hG hC)=> B hB.
    apply/seteqP; split=> x; last by move=> [].
    move=> [hxB hxC]; have hxR := hCR x hxC.
    apply: hxR.2; by exists B.
  have hp := (hEligible C hC).2.2.
  by rewrite hNewEmpty (measure_empty hm) ltxx in hp.
exists G; split; first exact hCount0.
split; first exact: maximal_disjoint_family_members hG.
split; [exact hDis|exact hZero].
Qed.

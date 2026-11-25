(** Federer (1969), 3.2.46, p. 282: local measure
    problems reduce to countably many coordinate patches.
    This supporting general-topology lemma globalises actual
    partial-function measurability, using 2.3.2, p. 73,
    and the countable measure laws of 2.1.3, pp. 55–56. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction MeasureCountableClosure MeasureIndexedCover
  MeasurableFunctionUP MeasurableRestrictionTransfer NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_local_function_measurability]:
    measurability on actual open neighbourhoods gives global
    measurability of the same partial graph, supporting
    3.2.46, p. 282. A countable base suffices; no
    boundedness, finite mass, total representative or globally
    selected patch is assumed. *)
Theorem measure_local_function_measurability (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (U : nat -> set X) (f : partial_function X Y) :
  is_measure mu -> is_countable_open_base U ->
  (forall V, open V -> measure_measurable mu V) ->
  (forall x, exists V : set X, open V /\ V x /\
    is_measure_measurable_function (measure_restrict mu V) f) ->
  is_measure_measurable_function mu f.
Proof.
move=> hMu hBase hOpenMeas hLocal.
pose C := [set V : set X | open V /\
  is_measure_measurable_function (measure_restrict mu V) f].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hF]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
constructor.
- pose N := ~` partial_function_domain f.
  have hNCover : N `<=` \bigcup_(V in G) (V `&` N).
    move=> x hx; have [V hVG hxV] := hGCover x Logic.I.
    exists V; first exact hVG; by split.
  have hPiece V (hVG : G V) : mu (V `&` N)=0.
    exact: measurable_function_domain (hGC V hVG).2.
  have hBound := measure_indexed_cover hMu hCount hNCover.
  rewrite (nonnegative_sum_zero hPiece) in hBound.
  by apply/eqP; rewrite eq_le hBound (measure_nonnegative hMu).
- move=> W hW.
  pose P := partial_function_preimage f W.
  have hPiece V (hVG : G V) : measure_measurable mu (P `&` V).
    exact (@measurable_restriction_intersection_transfer R X mu hMu V P
      (hOpenMeas V (hGC V hVG).1)
      (measurable_function_open_preimage (hGC V hVG).2 hW)).
  have hP : P=\bigcup_(V in G) (P `&` V).
    apply/seteqP; split=> x.
    + move=> hx; have [V hVG hxV] := hGCover x Logic.I.
      exists V; first exact hVG; by split.
    + by move=> [V hVG [hx _]].
  change (measure_measurable mu P); rewrite hP.
  exact (@measure_measurable_countable_union R X [the choiceType of set X]
    mu hMu G (fun V=>P `&` V) hCount hPiece).
Qed.

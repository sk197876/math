(** Federer (1969), 3.3.14, p. 298: actual finite restriction
    and open approximation give preservation of EVERY original null subset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions StructureProjectionConditions MeasureUP MeasureBasic MeasureRestriction
  MeasureAlmostBasic BorelRegularMeasureUP BorelRegularRestriction FiniteBorelOpenInfimum TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_open_bound_null_preservation]: the final
    open-approximation argument proving original (I) in Federer
    3.3.14, p. 298. The actual finite Borel restriction gives the
    proved open-infimum law; EVERY original subset B of E is kept,
    including nonmeasurable subsets. The original projection and
    original image remain. All restriction regularity and finite
    whole-restriction premises are derived, not supplied separately. *)
Lemma structure_open_bound_null_preservation (R:realType) n m
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_measure mu ->is_borel_regular_measure mu ->borel_set E ->mu E< +oo ->
  (forall O,open O ->euclidean_lebesgue_measure m
    (euclidean_projection_linear p @` (E `&` O))<=mu (E `&` O)) ->
  structure_projection_preserves_null_subsets mu E p.
Proof.
move=>hMu hRegular hE hFinite hOpen B hBE hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose nu:=measure_restrict mu E.
have hNu:is_measure nu:=measure_restrict_is_measure hMu E.
have hNuRegular:is_borel_regular_measure nu:=borel_regular_restrict_borel hMu hRegular hE.
have hNuFinite:nu setT< +oo by rewrite /nu /measure_restrict setIT.
pose L:=@euclidean_lebesgue_measure R m.
have hL:=euclidean_lebesgue_is_measure R m.
have hBound:L (euclidean_projection_linear p @` B)<=nu B.
  apply:(@finite_borel_regular_open_infimum R [the metricType R of X] nu B
    (L (euclidean_projection_linear p @` B)) hNu hNuRegular hNuFinite)=>O hO hBO.
  apply:le_trans _ (hOpen O hO).
  apply:(@measure_mono R [the choiceType of Y] L hL)=>y [x hx <-].
  exists x; last by [].
  split; [exact:hBE x hx|exact:hBO x hx].
have hInter:E `&` B=B.
  apply/seteqP; split; first by move=>x [_ hx].
  by move=>x hx; split; first exact:hBE x hx.
rewrite /nu /measure_restrict hInter hNull in hBound.
apply/eqP; rewrite eq_le (measure_nonnegative hL) andbT.
exact:hBound.
Qed.

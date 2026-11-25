(** Federer (1969), 4.1.7, p. 359:
    pullback of L1 fields for the
    weighted image measure retains their original
    conull partial domains. This supporting
    measurable-composition adapter combines the Borel
    version of 2.3.6, p. 77, with
    image-null invariance of 2.4.18, pp. 90–91. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionPrecomposition MeasureUP
  MeasureAlmostBasic MeasureAlmostEquality MeasurePushforward PushforwardAlmostEquality
  MeasurableFunctionUP MeasurableGraphEquivalence MeasurableAlmostModification
  BorelFunctionUP BorelFunctionBasic BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity
  CountablyMeasurableUP LusinBorelVersion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [radon_image_partial_measurable_precompose]:
    a measurable field for f#mu pulls
    back measurably to mu when its
    original Radon image domain is countably
    finite and its coefficient range is
    separable, supporting Federer 4.1.7, p. 359.
    No finite total measure is assumed. *)
Theorem radon_image_partial_measurable_precompose (R:realType)
    (X Y:topologicalType) (Z:metricType R)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (f:X->Y) (hf:continuous f)
    (hn:is_radon_measure (measure_pushforward f mu))
    (D:set Z) (z0:Z) (g:partial_function Y Z):
  countable D->dense D->measure_countably_measurable (measure_pushforward f mu) setT->
  is_measure_measurable_function (measure_pushforward f mu) g->
  is_measure_measurable_function mu (partial_function_precompose f g).
Proof.
move=>hCount hDense hFinite hG.
have hMeasure:=@measure_pushforward_is_measure R X Y f mu hm.
have [b [hBorel hAgree]]:=@lusin_borel_version_radon R Y Z
  (measure_pushforward f mu) hMeasure hn D g z0 hCount hDense hG hFinite.
have hComposition:=borel_function_composition (continuous_borel_function hf) hBorel.
have hTotal:is_measure_measurable_function mu (partial_function_total (fun x=>b (f x))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>A hA;rewrite partial_function_total_preimage.
    exact:(borel_regular_borel_measurable hm (radon_borel_regular hm hr) (hComposition A hA)).
have hPreTotal:=measurable_function_graph_equivalent
  (fun x z=>iff_sym (partial_function_precompose_total f b x z)) hTotal.
have hPreAgree:=@pushforward_almost_equal_precompose R X Y Z mu f g (partial_function_total b) hAgree.
exact:(measurable_function_almost_equal hm hPreTotal (measure_almost_equal_sym hPreAgree)).
Qed.

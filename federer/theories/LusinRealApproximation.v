(** Federer (1969), 2.3.6, p. 77, second corollary: a continuous real map
    differs from f on only a small part of A. Source context and Tietze
    background: TietzeNormalisation.v. Undefined values count as
    disagreement, consistently with 2.3.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealLineSeparability PartialFunctionUP
  PartialFunctionBasic PartialContinuityUP MeasureUP MeasureBasic MeasurableFunctionUP
  BorelRegularMeasureUP RadonMeasureUP LusinMetric LusinRadon LusinRealClosedExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_real_approximation_metric]: direct second
    corollary of Federer 2.3.6, p. 77, for a Borel regular
    measure on a metric source; normality is retained explicitly. *)
Theorem lusin_real_approximation_metric (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (hn : normal_space X) (A : set X) (f : partial_function X (real_line_metric R)) (e : R) :
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < e)%R -> exists h : X -> real_line_metric R, continuous h /\
    mu (A `\` partial_function_agreement f (partial_function_total h)) < e%:E.
Proof.
move=> hf hA hfin he; have [D [hc hd]] := real_line_countable_dense R.
have [C [hC [hCA [herr hcont]]]] := @lusin_borel_regular R X (real_line_metric R) mu hm hr
  D A f e hc hd hf hA hfin he.
have [h [hh ha]] := @lusin_real_closed_extension R X hn C f hC hcont.
exists h; split=> //; apply: le_lt_trans _ herr.
apply: (@measure_mono R X mu hm)=> x [hx hnC]; split=> // hc'.
apply: hnC; exact: ha x hc'.
Qed.

(** Source for [lusin_real_approximation_radon]: direct second
    corollary of Federer 2.3.6, p. 77, for a Radon measure
    on a normal locally compact Hausdorff source. *)
Theorem lusin_real_approximation_radon (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (hn : normal_space X) (A : set X) (f : partial_function X (real_line_metric R)) (e : R) :
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < e)%R -> exists h : X -> real_line_metric R, continuous h /\
    mu (A `\` partial_function_agreement f (partial_function_total h)) < e%:E.
Proof.
move=> hf hA hfin he; have [D [hc hd]] := real_line_countable_dense R.
have [C [hC [hCA [herr hcont]]]] := @lusin_radon R X (real_line_metric R) mu hm hr
  D A f e hc hd hf hA hfin he.
have hclosed : closed C := compact_closed (radon_hausdorff hr) hC.
have [h [hh ha]] := @lusin_real_closed_extension R X hn C f hclosed hcont.
exists h; split=> //; apply: le_lt_trans _ herr.
apply: (@measure_mono R X mu hm)=> x [hx hnC]; split=> // hc'.
apply: hnC; exact: ha x hc'.
Qed.

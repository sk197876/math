(** Federer (1969), 2.9.22, pp. 167–168: measurability and essential
    separability for the actual vector derivative integral in the extension
    of 2.9.20(1), p. 165. Difference quotients of a Banach-valued locally BV
    curve belong to A(L^1,Y), by the countable discontinuity theorem,
    separable range and the proved vector operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground CompleteMetricUP
  BVCurveBorel BorelFunctionUP BorelFunctionBasic BorelRegularMeasureUP
  ModuleQuotient ClosedLinearSpanUP CurveSeparableLinearEnvelope CurveArcLength
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableTotalNormedArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_map_measure_measurable]: supporting passage
    from the Borel curve to measurable difference quotients in Federer
    2.9.22, pp. 167–168, using 2.2.14, p. 70, and 2.3.2,
    p. 73. A total Borel map is measurable for any Borel regular
    source measure; no separability of its target is required. *)
Lemma borel_map_measure_measurable (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (f : X -> Y) : is_measure mu ->
  is_borel_regular_measure mu -> is_borel_function f ->
  is_measure_measurable_function mu (partial_function_total f).
Proof.
move=> hm hr hf; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U hU; rewrite partial_function_total_preimage.
  exact (@borel_regular_borel_measurable R X mu hm hr _ (hf U hU)).
Qed.

(** Source for [complete_normed_bv_shift_measurable]: supporting
    translated curves in Federer 2.9.22, pp. 167–168, for the
    actual derivative integral. Translation is continuous; the Borel
    curve and its shifts share the same closed separable linear
    envelope from 2.5.16, p. 110. Thus they belong to A(L^1,Y),
    even when the ambient Banach space is nonseparable. *)
Lemma complete_normed_bv_shift_measurable (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g : R -> real_norm_metric_space hN) (h : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  is_measurable_normed_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun x : real_line_metric R => g (x+h))).
Proof.
move=> hY hg.
have hShift : continuous ((fun x => x+h) : real_line_metric R -> real_line_metric R).
  apply: (@metric_fixed_lipschitz_continuous R [the metricType R of real_line_metric R]
    [the metricType R of real_line_metric R] (fun x => x+h) 1 ler01)=> x y.
  rewrite !real_line_metric_distanceE mul1r.
  have he : x+h-(y+h)=x-y by ring.
  by rewrite he.
have hB := @borel_function_composition (real_line_metric R) (real_line_metric R)
  [the topologicalType of real_norm_metric_space hN] (fun x => x+h) g
  (continuous_borel_function hShift) (complete_metric_bv_curve_borel hY hg).
split.
- exact (@borel_map_measure_measurable R (real_line_metric R)
    [the topologicalType of real_norm_metric_space hN] (@lebesgue_scalar_measure R)
    (fun x => g (x+h)) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) hB).
- have [Z [_ [hRange hSep]]] := @curve_separable_linear_envelope R E N hN g hg.
  exists Z; split=> //.
  rewrite partial_function_total_preimage.
  have he : (fun x : real_line_metric R => g (x+h)) @^-1` [set y | ~Z y]=set0.
    apply/seteqP; split=> x; last by move=> [].
    move=> hn; apply: hn; apply: hRange; by exists (x+h).
  by rewrite he (measure_empty (lebesgue_scalar_is_measure R)).
Qed.

(** Source for [complete_normed_bv_difference_quotient_measurable]:
    supporting fixed-increment normed difference quotients in Federer
    2.9.22, pp. 167–168. Addition and scalar multiplication in
    A(L^1,Y) preserve essential separability and measurable graphs.
    The field convention also defines the auxiliary quotient at h=0;
    only positive reciprocal increments are used for derivative limits. *)
Lemma complete_normed_bv_difference_quotient_measurable (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g : R -> real_norm_metric_space hN) (h : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  is_measurable_normed_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun x : real_line_metric R => h^-1 *: (g (x+h)-g x))).
Proof.
move=> hY hg; have hm := lebesgue_scalar_is_measure R.
have hShift := @complete_normed_bv_shift_measurable R E N hN g h hY hg.
have hBase := @complete_normed_bv_shift_measurable R E N hN g 0 hY hg.
have heBase : (fun x : real_line_metric R => g (x+0))=g.
  by apply/funext=> x; rewrite addr0.
rewrite heBase in hBase.
have hNeg := @measurable_normed_total_scale R (real_line_metric R) E N hN
  (@lebesgue_scalar_measure R) hm (-1) g hBase.
have heNeg : (fun x : real_line_metric R => (-1) *: g x)=(fun x => -g x).
  by apply/funext=> x; rewrite scaleN1r.
rewrite heNeg in hNeg.
have hDiff := @measurable_normed_total_add R (real_line_metric R) E N hN
  (@lebesgue_scalar_measure R) hm (fun x => g (x+h)) (fun x => -g x) hShift hNeg.
exact (@measurable_normed_total_scale R (real_line_metric R) E N hN
  (@lebesgue_scalar_measure R) hm h^-1 (fun x => g (x+h)-g x) hDiff).
Qed.

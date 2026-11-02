(** Federer (1969), 2.4.12, p. 87: finite-p norm homogeneity, used to
    normalise the functions in 2.4.14, p. 88. The proof uses abstract
    integral laws and retains infinite norm values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  PartialNormPower RealPower NormPowerScale ExtendedPositivePower ExtendedPowerProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence MeasureNonnegativeLowerIntegral
  MeasureLpNorm MeasureLpNormUP MeasureLpZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm_nonzero_scale]: supporting
    nonzero-scalar case of homogeneity in Federer 2.4.12,
    p. 87, used in the proof of 2.4.14, p. 88.
    The integral of the powered norm may be infinite. *)
Lemma measure_lp_norm_nonzero_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p c : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> c != 0%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p (partial_vector_scale c f) = `|c|%:E * measure_lp_norm mu N p f.
Proof.
move=> hp hc hf; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
have hcpos : (0 < `|c|)%R by rewrite normr_gt0.
have hcoef := @real_power_strictly_positive R `|c| p hcpos.
have [_ [b [hb he]]] := @measure_lp_norm_specification R X V N hN mu p f hm hp hf.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p f (measurable_function_domain hf).
have hb0 : 0 <= b.
  have hbLower := @measure_lower_integral_unique R X mu _ _ b
    (measure_lower_integral_specification mu _) hb.2.2.
  rewrite -hbLower; exact (@measure_lower_integral_nonnegative R X mu hm _ hnonneg).
have hscaled := @measure_integral_positive_scale R X mu hm (real_power `|c| p) _ b hcoef hb.
have hscaled' : is_measure_integral mu (partial_norm_power N p (partial_vector_scale c f))
    ((real_power `|c| p)%:E*b).
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hscaled)=> x z.
  exact (iff_sym (@partial_norm_power_scaled_graph R X V N hN f c p x z)).
have hcf := @measurable_normed_scalar_multiple R X V N hN mu hm c f hf.
rewrite (@measure_lp_norm_of_integral R X V N hN mu p _ _ hm hp hcf hscaled')
  (@extended_positive_power_positive_scale R (real_power `|c| p) p^-1 b hcoef hi hb0)
  (@real_power_root_cancel R `|c| p (normr_ge0 c) hp0) -he.
reflexivity.
Qed.

(** Source for [measure_lp_norm_scale]: full finite-p homogeneity assertion
    in Federer 2.4.12, p. 87 At scalar zero, the partial function retains
    its original conull domain and the right side uses zero times infinity
    equal to zero. *)
Theorem measure_lp_norm_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p c : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p (partial_vector_scale c f) = `|c|%:E * measure_lp_norm mu N p f.
Proof.
move=> hp hf; have [->|hc] := eqVneq c 0%R.
- rewrite normr0 mul0e.
  have hcf := @measurable_normed_scalar_multiple R X V N hN mu hm 0%R f hf.
  apply: (@lp_norm_zero_iff R X V N hN mu hm p _ hp hcf).2.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
  move=> x [y hy]; exists (0%R : real_norm_metric_space hN); split=> //.
  exists y; split=> //; by rewrite scale0r.
- exact (@measure_lp_norm_nonzero_scale R X V N hN mu hm p c f hp hc hf).
Qed.

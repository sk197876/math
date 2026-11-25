(** Federer (1969), 2.4.12, p. 86: the finite-p integral-root formula. These
    modules retain the possibly infinite value and exact partial domain. The
    abstract specification precedes its witness and sealed interface.
    Seminorm and completeness laws are separate results, not assumptions
    included in this specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormMetricContinuity RealPower
  PartialFunctionUP PartialFunctionPostcomposition PartialNormPower MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel MeasurablePostcomposition
  MeasurableExtendedRationalRays BorelFunctionBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_norm_positive_power]: measurability
    of the nonnegative integrand in Federer 2.4.12, p. 86,
    following the level-set criterion of 2.3.2(2), p. 73.
    Inverse positive powers identify the closed sublevels.
    The narrow num_normedtype import supplies only closed real
    order rays, as in GeometricQuantisationBorel.v. *)
Lemma measurable_norm_positive_power (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_norm_power N p f).
Proof.
move=> hp hf; have hd : measure_almost_everywhere mu
  (partial_function_domain (partial_norm_power N p f)).
  rewrite partial_norm_power_domain; exact: measurable_function_domain hf.
apply/(measurable_extended_rational_closed_lower_rays_iff hm hd)=> q.
rewrite /partial_norm_power partial_function_postcompose_preimage.
have hnorm : is_measure_measurable_function mu
  (partial_function_postcompose f (fun y => (N y : real_line_metric R))).
  apply: (@measurable_function_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space hN] (real_line_metric R)
    mu hm f (fun y => (N y : real_line_metric R)) hf).
  apply: continuous_borel_function; exact: real_norm_metric_norm_continuous.
have [hq|hq] := leP 0%R (ratr q : R).
- have he : [set y : real_norm_metric_space hN | (real_power (N y) p)%:E <= (ratr q : R)%:E] =
    [set y | (N y <= real_power (ratr q) p^-1)%R].
    apply/seteqP; split=> y hy.
    + have hy' : (real_power (N y) p <= ratr q)%R := hy.
      by rewrite (@real_power_le_root R (N y) (ratr q) p (real_seminorm_nonnegative hN.1 y) hq hp) in hy'.
    + change (real_power (N y) p <= ratr q)%R.
      by rewrite (@real_power_le_root R (N y) (ratr q) p (real_seminorm_nonnegative hN.1 y) hq hp).
  rewrite he -(@partial_function_postcompose_preimage X (real_norm_metric_space hN)
    (real_line_metric R) f (fun y => N y) [set y | (y <= real_power (ratr q) p^-1)%R]).
  apply: (@measurable_function_borel_preimage R X (real_line_metric R) mu hm _ hnorm).
  apply: closed_borel_set; exact: closed_le.
- have he : partial_function_preimage f
    [set y | (real_power (N y) p)%:E <= (ratr q : R)%:E] = set0.
    apply/seteqP; split=> x; last by move=> [].
    move=> [y [_ hy]].
    have hy' : (real_power (N y) p <= ratr q)%R := hy.
    move: hy'; rewrite leNgt.
    by rewrite (lt_le_trans hq (real_power_nonnegative (N y) p)).
  rewrite he; exact: measure_measurable_empty hm.
Qed.

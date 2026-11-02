(** Federer (1969), 3.2.6, pp. 245–246: a finite
    nonnegative density is positive at almost every point for
    its own measure. This supports recovery of arbitrary
    weights without adding source measurability hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureDensityUP MeasureDensityTransfer MeasureSubsetIntegral MeasureIntegralBounds MeasureUpperAlmostEquality
  MeasureDensityNullSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_density_positive_almost]: supporting
    positive-density reduction for the integral transformation in
    Federer 3.2.6, pp. 245–246, by the laws of
    2.4.10, p. 85. The exceptional zero-density set
    can have positive mass for the original measure. *)
Theorem finite_density_positive_almost (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:partial_function X (extended_real_line R)):
  is_measure_density mu h nu ->
  measure_almost_everywhere mu [set x|exists r:R,(0<=r)%R /\ partial_function_graph h x r%:E] ->
  measure_almost_everywhere nu [set x|exists r:R,(0<r)%R /\ partial_function_graph h x r%:E].
Proof.
move=>hNu hFinite.
pose P:=[set x|exists r:R,(0<r)%R /\ partial_function_graph h x r%:E].
have hZero:measure_almost_equal mu
    (partial_function_zero_extension (0:extended_real_line R) (~` P) h)
    (partial_function_total (fun _ :X=>(0:extended_real_line R))).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hFinite)=>x [r [hr hRx]].
  exists 0; split=>//.
  case:(pselect (P x))=>hx.
  - apply/partial_function_zero_extension_graph; right; split=>//; by move=>h; exact (h hx).
  - apply/partial_function_zero_extension_graph; left; split=>//.
    have hr0:r=0%R.
      apply/eqP; rewrite eq_le hr andbT leNgt; apply/negP=>hPos; apply:hx; by exists r.
    by rewrite hr0 in hRx.
rewrite /measure_almost_everywhere (hNu (~` P)) /measure_subset_upper_integral.
rewrite (@measure_upper_integral_almost_equal R X mu hm _ _ hZero).
exact:measure_upper_extended_zero hm.
Qed.

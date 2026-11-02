(** Federer (1969), 3.2.13, p. 250: the
    radial outer integral is restricted to positive
    radii. Negative-radius fibres are empty, and
    the zero radius is Lebesgue null. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialFunctionBasic LebesgueScalarMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [scalar_positive_ray_integral]: removal
    of negative and zero radii from the first
    polar integral in Federer 3.2.13, p. 250.
    Any signed partial integral is retained, including
    infinite values; nothing is assumed at radius zero. *)
Lemma scalar_positive_ray_integral (R:realType)
    (F:partial_function R (extended_real_line R)) a:
  (forall r,(r<0)%R ->partial_function_graph F r (0:extended_real_line R)) ->
  is_measure_integral (@lebesgue_scalar_measure R) F a ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R] F a.
Proof.
move=>hNeg hI.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
have hAway:measure_almost_everywhere mu [set r:R|r!=0].
  have hEq:(~` [set r:R|r!=0])=[set (0:R)].
    apply/seteqP; split=>r.
    - move=>hr; case:(eqVneq r 0)=>[he|hne]; first by rewrite he.
      exfalso; exact:hr hne.
    - move=>hr hn; have he:r=0 by exact hr.
      move:hn; change (r!=0 ->False); by rewrite he eqxx.
  rewrite /measure_almost_everywhere hEq; exact:lebesgue_scalar_singleton.
have hBoth:=measure_almost_everywhere_and hm hAway (measurable_function_domain hI.1).
apply:(measure_integral_almost_equal hm hI).
apply:(measure_almost_everywhere_mono hm _ hBoth)=>r [hr [z hz]].
case:(ltP r 0)=>hr0.
- exists (0:extended_real_line R); split; first exact:hNeg r hr0.
  apply/partial_function_zero_extension_graph; right; split; last by [].
  move=>hPos; have hBad:=lt_trans hPos hr0; by rewrite ltxx in hBad.
- have hPos:0<r by rewrite lt_neqAle eq_sym hr hr0.
  exists z; split=>//; apply/partial_function_zero_extension_graph; left; by split.
Qed.

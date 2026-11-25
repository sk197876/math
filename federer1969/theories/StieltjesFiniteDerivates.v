(** Federer (1969), 2.9.19, p. 164: finite nonnegative derivates of the two
    induced measures and continuity of the curve hold simultaneously outside
    Lebesgue-null exceptional sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealMetricCompleteness CurveArcLength CurveDiscontinuities
  ScalarLebesgueBallContext ScalarIntervalDerivationContext LebesgueScalarMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDerivates PartialFunctionUP
  DerivationExistence StieltjesImageMeasures StieltjesDerivationClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_finite_derivate_points]: supporting simultaneous
    finite derivate values for psi+ and psi- in Federer 2.9.19, p. 164 Both
    finite real witnesses are nonnegative and satisfy the actual partial
    derivate graphs for the printed interval relation. *)
Definition stieltjes_finite_derivate_points (R : realType)
    (psip psim : set (real_line_metric R) -> \bar R) : set (real_line_metric R) :=
  [set x | exists p m : R, 0<=p /\ 0<=m /\
    partial_function_graph (measure_derivate psip (@lebesgue_scalar_measure R)
      (@scalar_nondegenerate_interval_relation R)) x p%:E /\
    partial_function_graph (measure_derivate psim (@lebesgue_scalar_measure R)
      (@scalar_nondegenerate_interval_relation R)) x m%:E].

(** Source for [stieltjes_induced_derivates_finite_ae]: direct application
    of 2.9.5 in Federer 2.9.19, p. 164, for both measures of an arbitrary
    induced pair. The reference and both numerators satisfy the original
    class M; the two exceptional sets have null union. *)
Lemma stieltjes_induced_derivates_finite_ae (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    (stieltjes_finite_derivate_points psip psim).
Proof.
move=> hg hp.
have [hcp hcm] := stieltjes_induced_pair_derivation_class hg hp.
have hP := @federer_2_9_5 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip (@scalar_nondegenerate_interval_relation R)
  (scalar_interval_derivation_context R) hcp.
have hM := @federer_2_9_5 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim (@scalar_nondegenerate_interval_relation R)
  (scalar_interval_derivation_context R) hcm.
have hPM := measure_almost_everywhere_and (lebesgue_scalar_is_measure R) hP hM.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hPM).
move=> x [[p [hpD [hp0 hpfin]]] [m [hmD [hm0 hmfin]]]].
have hpf : p \is a fin_num by rewrite (ge0_fin_numE hp0).
have hmf : m \is a fin_num by rewrite (ge0_fin_numE hm0).
exists (fine p),(fine m).
have hp0r : 0<=fine p by move: hp0; rewrite -(fineK hpf) lee_fin.
have hm0r : 0<=fine m by move: hm0; rewrite -(fineK hmf) lee_fin.
split=> //; split=> //; by rewrite !fineK.
Qed.

(** Source for [real_bv_continuity_ae]: supporting removal of discontinuity
    points in the proof of Federer 2.9.19, p. 164, using countability from
    2.5.16, p. 109. Scalar Lebesgue measure annihilates the countable jump
    set; no global continuity assumption is imposed on g. *)
Lemma real_bv_continuity_ae (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | g @ x --> g x].
Proof.
move=> hg.
have hnull := @scalar_lebesgue_countable_null R (curve_jump_points g)
  (@curve_jump_points_countable R [the metricType R of real_line_metric R] g hg).
apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hnull).
move=> x hn; exact ((@curve_jump_points_iff R [the metricType R of real_line_metric R]
  g hg (@real_line_metric_complete R) x).2 hn).
Qed.

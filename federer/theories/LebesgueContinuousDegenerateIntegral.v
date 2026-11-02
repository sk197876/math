(** Supporting flat-image case of Federer (1969), 2.9.21, p. 166: an
    increasing absolutely continuous curve may have equal endpoint values.
    The continuous Lebesgue/Riemann identity from 2.5.17, p. 111, is
    supplemented by its zero-length case. compare the weak increasing
    convention of Federer 2.5.18(2), p. 112. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  SummableRealFunctionUP MeasureSubsetIntegral NullSubsetIntegral LebesgueScalarMeasure
  CurveVariationUP CurveArcLength StieltjesIntegral StieltjesMonotone
  LebesgueRiemannContinuous.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_continuous_segment_integral_including_diagonal]:
    supporting flat-image extension for Federer 2.9.21, p. 166,
    of the continuous interval identity from 2.5.17, p. 111.
    The singleton target has zero Lebesgue measure and the
    Riemann-Stieltjes integral with identity integrator is zero.
    No strict monotonicity of the changing variable is introduced. *)
Lemma lebesgue_continuous_segment_integral_including_diagonal (R : realType)
    (f : R -> R) (a b : R) : continuous (f : real_line_metric R -> real_line_metric R) ->
  a<=b -> is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand f) (stieltjes_integral (fun x : R => x) f a b)%:E.
Proof.
move=> hf hab; case: (eqVneq a b)=> [habEq|habNe].
- rewrite -habEq.
  have hId : curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
    apply: monotone_locally_finite_variation; by move=> x y hxy.
  have hfBound x : a<=x<=a -> `|f x|<=`|f a|.
    move=> /andP[hax hxa].
    have he : x=a by apply/eqP; rewrite eq_le hxa hax.
    by rewrite he.
  have hBound := @stieltjes_integral_bound R (fun x : R => x) hId f a a `|f a|
    hf (lexx a) hfBound.
  rewrite /total_variation curve_variation_self fine0 mulr0 in hBound.
  have hZero : stieltjes_integral (fun x : R => x) f a a=0.
    have hn : `|stieltjes_integral (fun x : R => x) f a a|=0.
      by apply/le_anti/andP; split=> //; exact: normr_ge0.
    by move/eqP: hn; rewrite normr_eq0=> /eqP.
  rewrite hZero.
  apply: null_target_subset_integral (lebesgue_scalar_is_measure R) _.
  have he : (`[a,a] : set (real_line_metric R))=[set a].
    apply/seteqP; split.
    - move=> x; rewrite /= in_itv /= => /andP[hax hxa].
      by apply/eqP; rewrite eq_le hxa hax.
    - move=> x ->; by rewrite /= in_itv /= lexx.
  by rewrite he lebesgue_scalar_singleton.
- have hab' : a<b by rewrite lt_neqAle habNe hab.
  exact: lebesgue_riemann_continuous_segment hf hab'.
Qed.

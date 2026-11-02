(** Federer (1969), 2.9.22, p. 167, Lipschitz case: scalarisations by
    elements of Y* have derivatives on a common conull set for a countable
    family F. This file derives their BV hypotheses and the quotient bounds
    from the Lipschitz estimate. it does not state the reflexive-Banach
    extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  RealFunctionalNormUP ContinuousDualUP CurveArcLength LipschitzCurveVariation
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure
  RealCurveDerivativeUP RealBVMonotoneDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_lipschitz_scalarisation]: supporting
    Lipschitz bound for alpha o g in Federer 2.9.22, p. 167.
    Its constant is |alpha| L by the abstract dual norm laws. *)
Lemma normed_lipschitz_scalarisation (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E) (L : R) :
  (forall t u, N (g t-g u)<=L * `|t-u|) -> forall a t u,
  `|ed a (g t)-ed a (g u)|<=(DN a * L) * `|t-u|.
Proof.
move=> hg a t u.
rewrite -(linearB (hom_as_linear (ed a)) (g t) (g u)) hom_as_linearE.
have hB := real_functional_norm_bound (continuous_dual_norm_laws hD a) (g t-g u).
have hn := real_functional_norm_nonnegative (continuous_dual_norm_laws hD a).
have hmul := ler_wpM2l hn (hg t u).
rewrite mulrA in hmul.
exact: le_trans hB hmul.
Qed.

(** Source for [normed_lipschitz_difference_quotient_bound]: the
    bound on all nonzero difference quotients used in the dual
    approximation of Federer 2.9.22, p. 167. Cancellation
    uses the positive absolute value of the increment. *)
Lemma normed_lipschitz_difference_quotient_bound (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (L x : R) :
  (forall t u, N (g t-g u)<=L * `|t-u|) -> forall h,
  h!=0 -> N (h^-1 *: (g (x+h)-g x))<=L.
Proof.
move=> hg h hn.
have hb := hg (x+h) x; rewrite addrAC subrr add0r in hb.
have hh : 0<`|h| by rewrite normr_gt0.
by rewrite (real_seminorm_scale hN.1) normfV mulrC ler_pdivrMr.
Qed.

(** Source for [lipschitz_dual_derivatives_common_ae]: the
    common conull set where (beta o g)' exists for every beta
    in countable F, Federer 2.9.22, p. 167. The countable
    intersection is proved explicitly; no uncountable intersection
    of almost-everywhere assertions is taken. *)
Theorem lipschitz_dual_derivatives_common_ae (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E)
    (L : R) (F : set D) :
  countable F -> (forall t u, N (g t-g u)<=L * `|t-u|) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | forall a, F a -> exists v, has_real_curve_derivative (fun t => ed a (g t)) x v].
Proof.
move=> hF hg.
have hone a : measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v, has_real_curve_derivative (fun t => ed a (g t)) x v].
  have hs := @normed_lipschitz_scalarisation R E D N hN ed DN hD g L hg a.
  have hlip : forall t u, mdist (ed a (g t) : real_line_metric R) (ed a (g u))
      <=(DN a * L) * `|t-u| := hs.
  have hf := @lipschitz_curve_locally_finite_variation R
    [the metricType R of real_line_metric R] (fun t => ed a (g t)) (DN a * L) hlip.
  have hd := real_bv_joint_derivatives_ae hf.
  apply: (@measure_almost_everywhere_mono R (real_line_metric R)
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hd).
  by move=> x [v [w [hv _]]]; exists v.
have hc := @measure_almost_everywhere_countable R (real_line_metric R) D
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) F
  (fun a => [set x | exists v, has_real_curve_derivative (fun t => ed a (g t)) x v])
  hF (fun a _ => hone a).
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hc).
by move=> x hx a ha; exact: hx a ha.
Qed.

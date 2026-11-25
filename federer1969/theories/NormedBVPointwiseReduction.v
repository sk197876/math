(** Federer (1969), 2.9.22, p. 168, final two alternatives after
    factorisation g=H o s: s'(x)=0 gives g'(x)=0, and existence of H'(s(x))
    gives g'(x)=s'(x)H'(s(x)). These pointwise implications use the already
    proved factorisation laws of 2.5.16, pp. 109–110. The exceptional-set
    transfer ensuring that the alternatives cover almost every x is a
    separate step. Chapter 21 has no corresponding reflexive-Banach
    differentiation item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import RealNormUP NormMetric CurveArcLength CurveLipschitzFactor CurveBanachExtension
  RealCurveDerivativeUP NormedCurveDerivativeUP NormedDerivativeBounds NormedCurveChainRule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_bv_zero_arc_derivative]: direct first
    alternative in Federer 2.9.22, p. 168. The distance
    estimate of 2.5.16, p. 109, and s'(x)=0 force an
    actual norm derivative g'(x)=0. Completeness and reflexivity
    are unnecessary for this particular implication. *)
Theorem normed_bv_zero_arc_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g : R -> real_norm_metric_space hN) (x : R) :
  curve_locally_finite_variation g ->
  has_real_curve_derivative (arc_length g) x 0 ->
  has_normed_curve_derivative N g x 0.
Proof.
move=> hg hs.
have hcontrol h : N (g (x+h)-g x)<=`|arc_length g (x+h)-arc_length g x|.
  exact: arc_length_distance_abs hg (x+h) x.
exact (@normed_curve_zero_derivative_from_control R E N hN g (arc_length g) x hcontrol hs).
Qed.

(** Source for [normed_bv_factor_derivative]: direct second
    pointwise alternative in Federer 2.9.22, p. 168, using
    its actual factorisation H o s=g. The proved norm chain
    rule also includes zero s'(x) when H'(s(x)) exists;
    this does not assume that H' exists at every image point. *)
Theorem normed_bv_factor_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g H : R -> real_norm_metric_space hN) (x w : R) (v : E) :
  is_curve_banach_extension g H -> has_real_curve_derivative (arc_length g) x w ->
  has_normed_curve_derivative N H (arc_length g x) v ->
  has_normed_curve_derivative N g x (w *: v).
Proof.
move=> hH hs hder.
have he : (fun t => H (arc_length g t))=g.
  apply/funext=> t; exact (@curve_banach_compose R E N hN g H hH t).
have hd := @normed_curve_derivative_compose R E N hN H (arc_length g) x w v hs hder.
by rewrite he in hd.
Qed.

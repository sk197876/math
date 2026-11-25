(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, proof of lem:DGPR31, (eq:31:J): if
    0 < rho <= S, ∫ rho = γ and ∫ S = M, then
    γ log(γ/M) <= ∫ rho log(rho/S) <= 0. The blueprint applies Jensen's
    inequality (Federer 2.4.19) to the probability measure M^(-1) S L^n
    and the convex function [r ↦ r log r]; here the same bound follows
    from the tangent line of [r ↦ r log r] at a = γ/M, which is the
    content of Jensen's inequality for this function, integrated against
    S (Federer 2.4.4, p. 82). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal lra ring.
From Federer Require Import PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic RealTotalCharacteristicBounds
  RealExponentialUP RealExponentialSealed RealExponentialLaws EuclideanLebesgueDimensions
  GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section EntropyBound.
Variable R : realType.
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_entropy_tangent]: the tangent line of the convex
    function [r ↦ r log r] at a > 0 lies below it on (0,∞), from
    log(a/r) <= a/r - 1; proof of lem:DGPR31, (eq:31:J). *)
Lemma dgpr_entropy_tangent (a r : R) : 0 < a -> 0 < r ->
  a * LOG a + (1 + LOG a) * (r - a) <= r * LOG r.
Proof.
move=> ha hr.
have ht := real_logarithm_tangent (divr_gt0 ha hr).
rewrite real_logarithm_ratio // in ht.
have h : r * (LOG a - LOG r) <= r * (a / r - 1) by rewrite ler_pM2l.
have e1 : r * (a / r - 1) = a - r by field; rewrite gt_eqF.
have e2 : a * LOG a + (1 + LOG a) * (r - a) = r * LOG a + (r - a) by ring.
rewrite e1 mulrBr in h; rewrite e2.
move: h; set p := r * LOG a; set q := r * LOG r; lra.
Qed.

Variable X : choiceType.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [dgpr_entropy_jensen]: (eq:31:J) of the proof of
    lem:DGPR31 in integrated form: if 0 < rho <= S, the integrals of
    rho and S are γ > 0 and M > 0, and J is the integral of
    rho log(rho/S), then γ log(γ/M) <= J <= 0. *)
Theorem dgpr_entropy_jensen (rho S : X -> R) (gamma M J : R) :
  0 < gamma -> 0 < M ->
  (forall x, 0 < rho x <= S x) ->
  is_measure_integral mu (real_total_integrand rho) gamma%:E ->
  is_measure_integral mu (real_total_integrand S) M%:E ->
  is_measure_integral mu (real_total_integrand (fun x => rho x * LOG (rho x / S x))) J%:E ->
  gamma * LOG (gamma / M) <= J <= 0.
Proof.
move=> hg hM hrS hr hS hJ.
have hS0 x : 0 < S x by have /andP[h1 h2] := hrS x; exact: lt_le_trans h1 h2.
have hq x : 0 < rho x / S x by have /andP[h1 _] := hrS x; rewrite divr_gt0.
apply/andP; split.
- pose a := gamma / M.
  have ha : 0 < a by rewrite divr_gt0.
  have eaM : a * M = gamma by rewrite /a divfK ?gt_eqF.
  have h1 := real_total_integral_scale hm (a * LOG a) hS.
  have h2 := real_total_integral_scale hm a hS.
  have h3 := real_total_integral_subtract hm hr h2.
  have h4 := real_total_integral_scale hm (1 + LOG a) h3.
  have h5 := real_total_integral_add hm h1 h4.
  have hle : forall x, a * LOG a * S x + (1 + LOG a) * (rho x - a * S x) <= rho x * LOG (rho x / S x).
    move=> x; have ht := dgpr_entropy_tangent ha (hq x).
    have hSx := hS0 x.
    have e1 : a * LOG a * S x + (1 + LOG a) * (rho x - a * S x) =
        S x * (a * LOG a + (1 + LOG a) * (rho x / S x - a)).
      by field; rewrite gt_eqF.
    have e2 : rho x * LOG (rho x / S x) = S x * (rho x / S x * LOG (rho x / S x)).
      by rewrite mulrA mulrCA divff ?gt_eqF // mulr1.
    by rewrite e1 e2 ler_pM2l.
  have hmono := measure_integral_monotone hm h5 hJ (real_total_pointwise_order_almost hm hle).
  rewrite lee_fin in hmono; apply: le_trans hmono.
  by rewrite eaM subrr mulr0 addr0 -/a mulrAC eaM.
- have h0 := real_total_integral_scale hm 0 hr.
  have hle : forall x, rho x * LOG (rho x / S x) <= 0 * rho x.
    move=> x; have /andP[h1 h2] := hrS x; rewrite mul0r.
    have hlog : LOG (rho x / S x) <= 0.
      rewrite -(real_logarithm_one R) real_logarithm_order //.
      by rewrite ler_pdivrMr ?mul1r // hS0.
    by rewrite mulr_ge0_le0 // ltW.
  have hmono := measure_integral_monotone hm hJ h0 (real_total_pointwise_order_almost hm hle).
  by rewrite lee_fin mul0r in hmono.
Qed.

End EntropyBound.

(** Source for [dgpr_entropy_jensen_lebesgue]: (eq:31:J) for the
    Lebesgue measure L^n on R^n, the case used in the proof of
    lem:DGPR31. *)
Corollary dgpr_entropy_jensen_lebesgue (R : realType) (n : nat) (rho S : R_n R n -> R) (gamma M J : R) :
  0 < gamma -> 0 < M ->
  (forall x, 0 < rho x <= S x) ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand rho) gamma%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand S) M%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x => rho x * RealExponential.logarithm (rho x / S x))) J%:E ->
  gamma * RealExponential.logarithm (gamma / M) <= J <= 0.
Proof. exact: (dgpr_entropy_jensen (@euclidean_lebesgue_is_measure R n)). Qed.

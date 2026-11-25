(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Theorem 1.1; blueprint dgpr_blueprint.tex, lem:compact_case, for
    normalised data.

    Assume (S) ([dgpr_standing]) for some 0 < T_0, with μ(R^n) = 1 and
    μ_0 = μ ⌞ E, where E ⊆ R^n is compact and m rectifiable,
    H^m(E) = h with 0 < h < ∞ and γ = μ_0(R^n) > 1/2. Since T enters (S)
    only through 0 < T, (S) holds for every 0 < T
    ([dgpr_standing_time]). Suppose C0 ≥ 0 is a constant for which the
    conclusion of lem:upper_entropy holds for these data and every
    0 < T. Then
        1 ≤ C h^(1/m) δ,
    where δ = ‖Υ‖(R^n), C = exp(C2), C2 = log 2 + C1 (1 + log 4),
    C1 = C0 + log c(n) + 2^(-1) n, and c(n) = 1 + 2 (4π)^(n/2) is the
    constant of lem:tube ([dgpr_compact_case_normalised]).

    The proof is that of the blueprint. Combining lem:upper_entropy at
    a time T − s_0 < τ < T with lem:lower_entropy and dividing by γ
    gives (eq:cc:main),
        log(γ/h) ≤ − 2^(-1) m log T + C1 (1 + log((1 + T^(1/2) δ)/γ))
    for 0 < T ([dgpr_compact_case_entropy]). If δ = 0, the choice
    T = exp(2 m^(-1) (C1 (1 + log γ^(-1)) − log(γ/h) + 1)) contradicts
    (eq:cc:main); hence δ > 0. The choice T = δ^(-2) and 1/2 < γ ≤ 1
    give − log 2 − log h ≤ m log δ + C1 (1 + log 4), that is,
    h δ^m ≥ exp(−C2), and C h^(1/m) δ ≥ exp(C2/m) h^(1/m) δ ≥ 1.

    For the data of mr:hypotheses_main, lem:compact_case follows after
    the normalisation μ(R^n) = 1, the extension of X off M, the choice of
    the dual density dΥ of mr:functionals and of E by lem:inner; these
    reductions are not formalised here (docs/entropy.md).

    With the constant C0 of lem:upper_entropy
    ([dgpr_upper_entropy_constant], DgprUpperEntropy.v), which depends
    only on n, λ and Λ, the hypothesis on C0 is a theorem; this gives
    [dgpr_compact_case_standing]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  ProductInner InnerMetric PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction MeasureIntegralUP
  PartialFunctionBasic MeasureSubsetIntegral LebesgueScalarMeasure
  SummableRealFunctionUP RadonMeasureUP ScalarNormMetricCompleteness LocalUniquenessExample
  HausdorffMeasure RectifiableSetUP SmoothFunctionSpaceUP SmoothTestSpaces RealPower
  CircularTrigonometryUP CircularTrigonometrySealed CircularHalfPeriodLower
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprHeatKernel DgprStanding DgprHeatObjects DgprEntropy DgprLowerEntropy
  DgprUpperEntropy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CompactConstant.
Variable R : realType.
Variable n : nat.
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation EXP := (@RealExponential.exponential R).

(** Source for [dgpr_compact_case_C1]: blueprint proof of
    lem:compact_case, C1 = C0 + log c(n) + 2^(-1) n, with c(n) the
    constant of lem:tube. Definition. *)
Definition dgpr_compact_case_C1 (C0 : R) : R :=
  C0 + LOG (@dgpr_tube_constant R n) + 2^-1 * n%:R.

(** Source for [dgpr_compact_case_constant]: blueprint proof of
    lem:compact_case, C = exp(C2) with C2 = log 2 + C1 (1 + log 4).
    Definition. *)
Definition dgpr_compact_case_constant (C0 : R) : R :=
  EXP (LOG 2 + dgpr_compact_case_C1 C0 * (1 + LOG 4)).

(** Source for [dgpr_tube_constant_log_ge0]: log c(n) ≥ 0, since
    c(n) = 1 + 2 (4π)^(n/2) ≥ 1; proof of lem:compact_case. *)
Lemma dgpr_tube_constant_log_ge0 : 0 <= LOG (@dgpr_tube_constant R n).
Proof.
have hc := @dgpr_tube_constant_gt0 R n.
rewrite -(@real_logarithm_one R) real_logarithm_order //.
by rewrite /dgpr_tube_constant lerDl mulr_ge0 // exprn_ge0 // sqrtr_ge0.
Qed.

(** Source for [dgpr_compact_case_C1_ge0]: C1 ≥ 0 whenever C0 ≥ 0;
    proof of lem:compact_case. *)
Lemma dgpr_compact_case_C1_ge0 (C0 : R) : 0 <= C0 -> 0 <= dgpr_compact_case_C1 C0.
Proof.
move=> hC0; have hl := dgpr_tube_constant_log_ge0.
rewrite /dgpr_compact_case_C1; apply: addr_ge0; first exact: addr_ge0.
by apply: mulr_ge0; [rewrite invr_ge0 ler0n | exact: ler0n].
Qed.

(** Source for [dgpr_compact_case_constant_gt0]: 0 < C; proof of
    lem:compact_case. *)
Lemma dgpr_compact_case_constant_gt0 (C0 : R) : 0 < dgpr_compact_case_constant C0.
Proof. exact: real_exponential_positive (@RealExponential.laws R) _. Qed.
End CompactConstant.

Section CompactCase.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).
Local Notation HH := (@hausdorff_measure R RnM m).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation EXP := (@RealExponential.exponential R).
Local Notation hEL := (@RealExponential.laws R).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Variable Ec : set RnM.
Hypothesis hEc : mu0 = measure_restrict mu Ec.

(** Source for [dgpr_standing_time]: blueprint proof of
    lem:compact_case, "for each 0 < T < ∞, the hypotheses (S) hold": the
    number T enters (S) only through 0 < T. *)
Lemma dgpr_standing_time (T T' : R) :
  dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma -> 0 < T' ->
  dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T' mu0 gamma.
Proof. by move=> hS hT; case: hS => *; split. Qed.

(** Source for [dgpr_standing_restrict]: blueprint proof of
    lem:compact_case, "the hypotheses (S) hold with μ_0 = μ ⌞ E": μ ⌞ E
    is a measure (Federer 2.1.2), the open sets are μ ⌞ E measurable
    (Federer 2.1.2), μ ⌞ E ≤ μ, and (μ ⌞ E)(R^n) = μ(E). *)
Lemma dgpr_standing_restrict (T : R) (mu1 : set X -> \bar R) (gamma1 g : R) :
  dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu1 gamma1 ->
  mu Ec = g%:E -> 0 < g ->
  dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T (measure_restrict mu Ec) g.
Proof.
move=> hS hg hg0; have hmu := dgpr_standing_mu_measure hS.
case: hS => *; split => //.
- exact: measure_restrict_is_measure.
- by move=> A hA; apply: measure_restrict_measurable; auto.
- by move=> A; rewrite /measure_restrict; apply: measure_mono => // x [].
- by rewrite /measure_restrict setIT.
Qed.

(** Source for [dgpr_upper_entropy_property]: blueprint
    lem:upper_entropy (DPGPR 2026, (4.1)): its conclusion for the present
    data, every 0 < T and the constant C0, as used in the proof of
    lem:compact_case. Definition. *)
Definition dgpr_upper_entropy_property (C0 : R) : Prop :=
  forall (T : R) (hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma)
    (tau : R), 0 <= tau < T ->
  dgpr_entropy_tilde hS tau <=
    - (2^-1 * m%:R * gamma * LOG T) + C0 * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)).

(** Source for [dgpr_upper_entropy_property_of]: blueprint
    lem:upper_entropy ([dgpr_upper_entropy_of], DgprUpperEntropy.v): the
    conclusion of lem:DGPR32 with the constant C0 for the present data
    and every 0 < T gives [dgpr_upper_entropy_property C0]. *)
Lemma dgpr_upper_entropy_property_of (C0 : R) :
  (forall (T : R) (hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma)
     (s : R), 0 <= s < T ->
   (measure_subset_upper_integral (@lebesgue_scalar_measure R) `[0%R, s]
      (partial_function_total (fun t : R =>
         dgpr_fisher_information hS t - ((n - m)%N%:R * gamma / (2 * (T - t)))%:E))
    <= (C0 * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E) ->
  dgpr_upper_entropy_property C0.
Proof.
move=> h32 T hS tau htau.
exact: (dgpr_upper_entropy_of (h32 T hS) htau).
Qed.

Variable C0 : R.
Hypothesis hC0 : 0 <= C0.
Hypothesis hup : dgpr_upper_entropy_property C0.
Variable T0 : R.
Hypothesis hS0 : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T0 mu0 gamma.
Variable h : R.
Hypothesis hcE : compact Ec.
Hypothesis hrE : is_m_rectifiable m Ec.
Hypothesis hh : HH Ec = h%:E.
Hypothesis hh0 : 0 < h.
Local Notation C1 := (@dgpr_compact_case_C1 R n C0).

Let hg : 0 < gamma := dgpr_standing_gamma hS0.

Let hg1 : gamma <= 1.
Proof.
have h1 := dgpr_standing_mu0_le hS0 setT.
by rewrite (dgpr_standing_mu0_mass hS0) (dgpr_standing_mu_mass hS0) lee_fin in h1.
Qed.

Let hd0 : 0 <= delta.
Proof.
have h1 := measure_nonnegative (dgpr_standing_ups_measure hS0) setT.
by rewrite (dgpr_standing_ups_mass hS0) lee_fin in h1.
Qed.

(** Source for [dgpr_compact_case_entropy]: blueprint proof of
    lem:compact_case, (eq:cc:main): for 0 < T,
    log(γ/h) ≤ − 2^(-1) m log T + C1 (1 + log((1 + T^(1/2) δ)/γ)), by
    lem:upper_entropy and lem:lower_entropy at a time
    max {0, T − s_0/2}. *)
Lemma dgpr_compact_case_entropy (T : R) : 0 < T ->
  LOG (gamma / h) <=
    - (2^-1 * m%:R * LOG T) + C1 * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)).
Proof.
move=> hT; have hS := dgpr_standing_time hS0 hT.
have [s0 [hs0 hlow]] := dgpr_lower_entropy hS hEc hcE hrE hh hh0.
set tau := Num.max 0 (T - s0 / 2).
have ht1 : T - s0 < tau.
  by rewrite lt_max; apply/orP; right; rewrite ltrD2l ltrN2 ltr_pdivrMr // ltr_pMr // ltr1n.
have ht2 : tau < T by rewrite gt_max hT ltrBlDr ltrDl divr_gt0.
have ht0 : 0 <= tau by rewrite le_max lexx.
have hl := hlow tau ht1 ht2.
have hu := hup hS (introT andP (conj ht0 ht2)).
have hq : 0 <= LOG ((1 + Num.sqrt T * delta) / gamma).
  rewrite -(@real_logarithm_one R) real_logarithm_order //; last first.
    by rewrite divr_gt0 // ltr_wpDr // mulr_ge0 // sqrtr_ge0.
  rewrite ler_pdivlMr // mul1r; apply: le_trans hg1 _.
  by rewrite lerDl mulr_ge0 // sqrtr_ge0.
have hc := @dgpr_tube_constant_log_ge0 R n.
have hle := le_trans hl hu.
have e1 : gamma * LOG (gamma / h) - gamma * (LOG (@dgpr_tube_constant R n) + 2^-1 * n%:R) =
    gamma * (LOG (gamma / h) - (LOG (@dgpr_tube_constant R n) + 2^-1 * n%:R)) by ring.
have e2 : - (2^-1 * m%:R * gamma * LOG T) +
    C0 * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)) =
    gamma * (- (2^-1 * m%:R * LOG T) + C0 * (1 + LOG ((1 + Num.sqrt T * delta) / gamma))) by ring.
rewrite e1 e2 ler_pM2l // in hle.
move: hle hq hc; rewrite /dgpr_compact_case_C1.
set Lq := LOG ((1 + Num.sqrt T * delta) / gamma); set Lc := LOG (@dgpr_tube_constant R n).
move=> hle hq hc.
have hn : 0 <= 2^-1 * n%:R :> R by apply: mulr_ge0; [rewrite invr_ge0 ler0n | exact: ler0n].
have hx : (Lc + 2^-1 * n%:R) <= (Lc + 2^-1 * n%:R) * (1 + Lq).
  by rewrite -{1}[Lc + _]mulr1 ler_wpM2l ?addr_ge0 // lerDl.
have e3 : (C0 + Lc + 2^-1 * n%:R) * (1 + Lq) = C0 * (1 + Lq) + (Lc + 2^-1 * n%:R) * (1 + Lq) by ring.
rewrite e3; lra.
Qed.

(** Source for [dgpr_compact_case_delta_gt0]: blueprint proof of
    lem:compact_case: δ > 0, since for δ = 0 the right side of
    (eq:cc:main) tends to −∞ as T → ∞; explicitly, the choice
    T = exp(2 m^(-1) (C1 (1 + log γ^(-1)) − log(γ/h) + 1)) gives
    log(γ/h) ≤ log(γ/h) − 1. *)
Lemma dgpr_compact_case_delta_gt0 : 0 < delta.
Proof.
rewrite lt_neqAle hd0 andbT; apply/negP => /eqP e0.
have /andP [hm0 _] := hm.
have hm0' : (m%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
set A := C1 * (1 + LOG (1 / gamma)) - LOG (gamma / h) + 1.
have hT : 0 < EXP (2 / m%:R * A) := real_exponential_positive hEL _.
have h1 := dgpr_compact_case_entropy hT.
rewrite -e0 mulr0 addr0 (real_logarithm_exponential hEL) in h1.
have e1 : - (2^-1 * m%:R * (2 / m%:R * A)) = - A by field.
rewrite e1 /A in h1; lra.
Qed.

(** Source for [dgpr_compact_case_log_bound]: blueprint proof of
    lem:compact_case: with T = δ^(-2) and 1/2 < γ ≤ 1,
    − log 2 − log h ≤ m log δ + C1 (1 + log 4). *)
Lemma dgpr_compact_case_log_bound : 2^-1 < gamma ->
  - LOG 2 - LOG h <= m%:R * LOG delta + C1 * (1 + LOG 4).
Proof.
move=> hg2; have hd := dgpr_compact_case_delta_gt0.
have hT : 0 < delta ^- 2 by rewrite invr_gt0 exprn_gt0.
have h1 := dgpr_compact_case_entropy hT.
have es : Num.sqrt (delta ^- 2) * delta = 1.
  by rewrite sqrtrV ?exprn_ge0 ?ltW // sqrtr_sqr gtr0_norm // mulVf // gt_eqF.
have eL : LOG (delta ^- 2) = - (2 * LOG delta).
  by rewrite real_logarithm_inverse ?exprn_gt0 // dgpr_logarithm_natural_power.
rewrite es eL in h1.
have hC1 := dgpr_compact_case_C1_ge0 n hC0.
have hl4 : LOG ((1 + 1) / gamma) <= LOG 4.
  rewrite real_logarithm_order ?divr_gt0 //; last by lra.
  by rewrite ler_pdivrMr //; lra.
have hlg : - LOG 2 <= LOG gamma.
  rewrite -real_logarithm_inverse; last by lra.
  by rewrite real_logarithm_order ?invr_gt0 //; lra.
rewrite real_logarithm_ratio // in h1.
have hx := ler_wpM2l hC1 hl4.
move: h1 hx hlg; set Ld := LOG delta; set Lh := LOG h; set Lg := LOG gamma.
set L4 := LOG 4; set Lq := LOG ((1 + 1) / gamma); set L2 := LOG 2.
move=> h1 hx hlg.
have e : - (2^-1 * m%:R * - (2 * Ld)) = m%:R * Ld by field.
rewrite e in h1; lra.
Qed.

(** Source for [dgpr_compact_case_normalised]: DPGPR 2026, proof of
    Theorem 1.1, and blueprint lem:compact_case, for normalised data:
    1 ≤ C h^(1/m) δ with C = exp(C2), since h δ^m ≥ exp(−C2) and
    C2 ≥ C2/m. *)
Theorem dgpr_compact_case_normalised : 2^-1 < gamma ->
  1 <= dgpr_compact_case_constant n C0 * real_power h (m%:R)^-1 * delta.
Proof.
move=> hg2; have hd := dgpr_compact_case_delta_gt0.
have hb := dgpr_compact_case_log_bound hg2.
have /andP [hm0 _] := hm.
have hm1 : (1 : R) <= m%:R by rewrite ler1n.
have hmp : (0 : R) < m%:R by rewrite ltr0n.
have hC1 := dgpr_compact_case_C1_ge0 n hC0.
have hl2 : 0 <= LOG 2 by rewrite -(@real_logarithm_one R) real_logarithm_order //; lra.
have hl4 : 0 <= LOG 4 by rewrite -(@real_logarithm_one R) real_logarithm_order //; lra.
set C2 := LOG 2 + C1 * (1 + LOG 4).
have hC2 : 0 <= C2 by rewrite /C2 addr_ge0 // mulr_ge0 // addr_ge0.
rewrite /dgpr_compact_case_constant -/C2 real_power_positive_base //.
rewrite -(real_exponential_logarithm hEL hd) -!(real_exponential_add hEL).
rewrite -[X in X <= _](real_exponential_zero hEL) real_exponential_order.
have hC2m : (m%:R)^-1 * C2 <= C2.
  by rewrite ler_pdivrMl // ler_peMl.
have hx0 : 0 <= C2 + LOG h + m%:R * LOG delta by rewrite /C2; lra.
have hmi : 0 <= (m%:R : R)^-1 by rewrite invr_ge0 ltW.
have hx := mulr_ge0 hmi hx0.
have e : (m%:R)^-1 * (C2 + LOG h + m%:R * LOG delta) =
    (m%:R)^-1 * C2 + (m%:R)^-1 * LOG h + LOG delta.
  by field; rewrite gt_eqF.
rewrite e in hx; lra.
Qed.

End CompactCase.

Section CompactCaseStanding.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).
Local Notation HH := (@hausdorff_measure R RnM m).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation EXP := (@RealExponential.exponential R).
Local Notation hEL := (@RealExponential.laws R).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Variable Ec : set RnM.
Hypothesis hEc : mu0 = measure_restrict mu Ec.
Variable T0 : R.
Hypothesis hS0 : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T0 mu0 gamma.
Variable h : R.
Hypothesis hcE : compact Ec.
Hypothesis hrE : is_m_rectifiable m Ec.
Hypothesis hh : HH Ec = h%:E.
Hypothesis hh0 : 0 < h.

(** Source for [dgpr_compact_case_standing]: DPGPR 2026, proof of
    Theorem 1.1, and blueprint lem:compact_case, for normalised data
    satisfying (S) with μ_0 = μ ⌞ E and 1/2 < γ: 1 ≤ C h^(1/m) δ, where
    C = [dgpr_compact_case_constant n C0] and C0 is the constant of
    lem:upper_entropy ([dgpr_upper_entropy_constant]); C depends only on
    n, λ and Λ. *)
Theorem dgpr_compact_case_standing : 2^-1 < gamma ->
  1 <= dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam) *
    real_power h (m%:R)^-1 * delta.
Proof.
move=> hg2.
have hC0 := ltW (dgpr_upper_entropy_constant_gt0 hS0).
apply: (dgpr_compact_case_normalised hEc hC0 _ hS0 hcE hrE hh hh0 hg2).
move=> T hS tau htau; have hu := dgpr_upper_entropy hS htau.
by [].
Qed.
End CompactCaseStanding.

(** De Philippis, Gennaioli, Pigati and Rindler (2026), (4.1); blueprint
    dgpr_blueprint.tex, lem:upper_entropy.

    Assume (S) ([dgpr_standing]). If C0 is a constant with
      ∫_[0,τ] (I(ρ_t) − (n − m) γ / (2 (T − t))) dL^1 t
          ≤ C0 γ (1 + log((1 + T^(1/2) δ)/γ))      for 0 ≤ τ < T,
    the conclusion of lem:DGPR32, then
      H̃(ρ_τ) ≤ − 2^(-1) m γ log T + C0 γ (1 + log((1 + T^(1/2) δ)/γ))
    for 0 ≤ τ < T ([dgpr_upper_entropy_of]). With the constant
    C0 = 2n + C1 ((16 n + 6) Λ² + 16) of lem:DGPR32 ([dgpr_lemma_3_2],
    DgprLemma32Theorem.v), where C1 = (2n + 1)(32 Λ/(3 λ²))² + 32/(3 λ²),
    this is lem:upper_entropy ([dgpr_upper_entropy]); C0 depends only on
    n, λ and Λ ([dgpr_upper_entropy_constant]).

    The proof is that of the blueprint. By lem:entropy and the
    fundamental theorem of calculus (Federer 3.1.11),
      H(ρ_τ) − H(ρ_0) = ∫_[0,τ] I(ρ_t) dL^1 t,
      2^(-1) (n − m) γ (log T − log(T − τ)) = ∫_[0,τ] (n − m) γ / (2 (T − t)) dL^1 t,
    hence H̃(ρ_τ) − H̃(ρ_0) is the integral of the left side above. By
    lem:entropy, γ ≤ 1 and 4π > 1, H̃(ρ_0) ≤ − 2^(-1) m γ log T.

    [dgpr_upper_entropy_conditional] instantiates C0 with the constant
    2n + C1 ((16 n + 6) Λ² + 16) of [dgpr_lemma_3_2_conditional]
    (DgprLemma32Final.v), under the remaining hypotheses of that theorem
    (the differentials DB of B and the estimate eq:32:I with a constant
    C1 ≥ 0); its Gaussian decay hypotheses are supplied by
    lem:regularity (DgprRegularity.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  ProductInner PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureUpperIntegralMonotone MeasureIntegralGraphEquivalence
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP EuclideanLebesgueDimensions
  LebesgueScalarMeasure ScalarNormMetricCompleteness LocalUniquenessExample NormDifferentialUP
  NormClassOneUP NormHigherCurveDerivativeUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces RealCurveDerivativeUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularHalfPeriodLower
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprHomNorms DgprDifferentialCalculus DgprHeatKernel DgprHeatKernelFamily DgprHeatJetCalculus DgprStanding
  DgprHeatObjects DgprIdentities DgprLemma31 DgprLemma31Main DgprGrowthClasses DgprParameterIntegralSmooth
  DgprTimeIntegrals DgprLemma31Final DgprLemma32Final DgprRegularity DgprEntropy DgprLemma31Field
  DgprLemma32Pointwise DgprLemma32Theorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section TimeCalculus.
Variable R : realType.
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_segment_upper_integral_ge]: Federer 2.4.2-2.4.4 and
    2.4.10, pp. 81-85: if g <= phi on [a,b] and g has the integral G over
    [a,b], then G is at most the upper integral of phi over [a,b];
    the counterpart of [dgpr_segment_upper_integral_le]. *)
Lemma dgpr_segment_upper_integral_ge (a b G : R) (phi : R -> \bar R) (g : R -> R) :
  (forall t, a <= t <= b -> ((g t)%:E <= phi t)%E) ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g) G%:E ->
  (G%:E <= measure_subset_upper_integral L1 `[a, b] (partial_function_total phi))%E.
Proof.
move=> hphi /dgpr_segment_integralE hG.
have hm := lebesgue_scalar_is_measure R.
have eG := @measure_upper_integral_unique R R L1 _ _ G%:E
  (measure_upper_integral_specification _ _) hG.2.1.
rewrite -eG /measure_subset_upper_integral.
apply: measure_upper_integral_monotone => //.
apply: (@measure_almost_everywhere_mono R R L1 hm setT _ _ (measure_almost_everywhere_true hm)) => x _.
case: (boolP (a <= x <= b)) => hx.
- exists (g x)%:E, (phi x); split; [|split].
  + by apply/real_total_integrand_graph; rewrite hx.
  + by apply/partial_function_zero_extension_graph; left; split => //; rewrite in_itv.
  + exact: hphi.
- exists 0%E, 0%E; split; [|split].
  + by apply/real_total_integrand_graph; rewrite (negbTE hx).
  + apply/partial_function_zero_extension_graph; right; split => //.
    by rewrite /= in_itv /= (negbTE hx).
  + exact: lexx.
Qed.

(** Source for [dgpr_time_logarithm_derivative]: the derivative of
    [r ↦ − k log(T − r)] at t < T is k (T − t)^(-1) (Federer 3.1.1(3)
    and 3.1.11, chain rule); proof of lem:upper_entropy. *)
Lemma dgpr_time_logarithm_derivative (T k t : R) : t < T ->
  has_real_curve_derivative (fun r => - k * LOG (T + r * -1)) t (k / (T - t)).
Proof.
move=> ht; have hs : 0 < T + t * -1 by rewrite mulrN1 subr_gt0.
have hTt : T - t != 0 by rewrite subr_eq0 gt_eqF.
have [hl _] := @dgpr_real_curve_logarithm R.
have h2 := dgpr_real_curve_chain (dgpr_real_curve_affine T (-1) t) (hl _ hs).
have h3 := dgpr_real_curve_product (dgpr_real_curve_constant (- k) t) h2.
have e : 0 * LOG (T + t * -1) + - k * ((T + t * -1)^-1 * -1) = k / (T - t).
  by rewrite mulrN1 mul0r add0r; field; rewrite hTt.
by rewrite e in h3.
Qed.

(** Source for [dgpr_logarithm_four_pi]: log(4π) >= 0, since
    π >= 3 (Federer 3.3.19, p. 302, [circular_half_period_at_least_three]);
    proof of lem:upper_entropy. *)
Lemma dgpr_logarithm_four_pi : 0 <= LOG (4 * dgpr_pi R).
Proof.
have hp : 3 <= dgpr_pi R := @circular_half_period_at_least_three R.
rewrite -(@real_logarithm_one R) real_logarithm_order //; [lra | lra].
Qed.
End TimeCalculus.

(** Source for [dgpr_upper_entropy_constant]: DPGPR 2026, (4.1), and
    blueprint lem:upper_entropy: the constant C = 2n + C1 ((16 n + 6) Λ² + 16)
    of lem:DGPR32, with C1 = (2n + 1)(32 Λ/(3 λ²))² + 32/(3 λ²); it
    depends only on n, λ and Λ. Definition. *)
Definition dgpr_upper_entropy_constant (R : realType) (n : nat) (lam Lam : R) : R :=
  2 * n%:R + dgpr_lemma32_C1 n lam Lam * ((16 * n%:R + 6) * Lam ^+ 2 + 16).

Section UpperEntropy.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
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
Local Notation NH := (hom_norm BX hCY heX).
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
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_upper_entropy_of]: DPGPR 2026, (4.1), and blueprint
    lem:upper_entropy, for every constant C0 satisfying the conclusion of
    lem:DGPR32. By lem:entropy and Federer 3.1.11,
    H̃(ρ_τ) − H̃(ρ_0) = ∫_[0,τ] (I(ρ_t) − (n − m) γ / (2 (T − t))) dL^1 t,
    and H̃(ρ_0) ≤ − 2^(-1) m γ log T by lem:entropy, γ ≤ 1 and 4π > 1. *)
Theorem dgpr_upper_entropy_of (C0 tau : R) :
  (forall s, 0 <= s < T ->
    (measure_subset_upper_integral L1 `[0%R, s]
       (partial_function_total (fun t : R =>
          dgpr_fisher_information hS t - ((n - m)%N%:R * gamma / (2 * (T - t)))%:E))
     <= (C0 * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E) ->
  0 <= tau < T ->
  dgpr_entropy_tilde hS tau <=
    - (2^-1 * m%:R * gamma * LOG T) + C0 * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)).
Proof.
move=> h32 htau; have /andP [h0 htT] := htau.
have hT := dgpr_standing_T hS.
have hg := dgpr_standing_gamma hS.
have hg1 : gamma <= 1.
  have h := dgpr_standing_mu0_le hS setT.
  by rewrite (dgpr_standing_mu0_mass hS) (dgpr_standing_mu_mass hS) lee_fin in h.
have [_ hIi hc1] := dgpr_entropy_derivative hS.
have hH := dgpr_before_ftc h0 htT hc1.
set k := (n - m)%N%:R * gamma / 2.
have hF2 t : t < T -> has_norm_differential A1 A1 [set s | s < T]%classic
    (fun r => - k * LOG (T + r * -1)) t (@scalar_coefficient_linear_map R R^o (k / (T - t))).
  by move=> ht; exact: (dgpr_before_curve_differential ht (dgpr_time_logarithm_derivative k ht)).
have hcz : norm_class_zero A1 A1 [set t | t < T]%classic (fun t => k / (T - t)).
  by apply: dgpr_before_curve_class_zero => t ht; exact: dgpr_time_reciprocal_derivative.
have hC := dgpr_before_ftc_general h0 htT hF2 hcz.
have hD := dgpr_segment_integral_add hH (dgpr_segment_integral_scale (-1) hC).
have hpt t : 0 <= t <= tau ->
    ((fine (dgpr_fisher_information hS t) + -1 * (k / (T - t)))%:E <=
     dgpr_fisher_information hS t - ((n - m)%N%:R * gamma / (2 * (T - t)))%:E)%E.
  move=> /andP [_ ht]; have htT' : t < T := le_lt_trans ht htT.
  have hTt : T - t != 0 by rewrite subr_eq0 gt_eqF.
  move: (dgpr_fisher_information_of (hIi t htT')).
  set a := fine (dgpr_fisher_information hS t) => e.
  rewrite e -EFinB lee_fin /k le_eqVlt; apply/orP; left; apply/eqP.
  by field; rewrite hTt.
have hle := le_trans (dgpr_segment_upper_integral_ge hpt hD) (h32 tau htau).
rewrite lee_fin mul0r addr0 mulrN1 in hle.
have hb := dgpr_entropy_initial_bound hS.
have h4 : 0 < 4 * dgpr_pi R by rewrite mulr_gt0 // (@dgpr_pi_gt0 R).
rewrite real_logarithm_product // in hb.
have hpi : 0 <= n%:R * gamma * LOG (4 * dgpr_pi R).
  by rewrite mulr_ge0 // ?dgpr_logarithm_four_pi // mulr_ge0 // ltW.
have hlg : gamma * LOG gamma <= 0.
  rewrite pmulr_rle0 // -(@real_logarithm_one R) real_logarithm_order //.
have hmn : (m <= n)%N by case/andP: hm.
rewrite /dgpr_entropy_tilde.
move: hle hb hpi hlg; rewrite /k natrB //.
set Ht := dgpr_entropy hS tau; set H0 := dgpr_entropy hS 0.
set Lt := LOG (T - tau); set LT := LOG T; set L4 := LOG (4 * dgpr_pi R); set Lg := LOG gamma.
set RHS := C0 * gamma * (1 + _).
move=> hle hb hpi hlg.
lra.
Qed.

(** Source for [dgpr_upper_entropy]: DPGPR 2026, (4.1), and blueprint
    lem:upper_entropy: for 0 ≤ τ < T,
    H̃(ρ_τ) ≤ − 2^(-1) m γ log T + C γ (1 + log((1 + T^(1/2) δ)/γ)), with
    the constant C of [dgpr_upper_entropy_constant], by
    [dgpr_upper_entropy_of] and lem:DGPR32 ([dgpr_lemma_3_2]) for a field
    DB of differentials of B ([dgpr_lemma31_DB_exists]). *)
Theorem dgpr_upper_entropy (tau : R) : 0 <= tau < T ->
  dgpr_entropy_tilde hS tau <=
    - (2^-1 * m%:R * gamma * LOG T) +
    dgpr_upper_entropy_constant n lam Lam * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)).
Proof.
have [DB hDB] := dgpr_lemma31_DB_exists hS.
apply: dgpr_upper_entropy_of => s hs.
exact: (dgpr_lemma_3_2 hDB hs).
Qed.

(** Source for [dgpr_upper_entropy_constant_gt0]: the constant of
    lem:upper_entropy is positive, since λ > 0 and n ≥ 1. *)
Lemma dgpr_upper_entropy_constant_gt0 : 0 < dgpr_upper_entropy_constant n lam Lam.
Proof.
have hC1 := dgpr_lemma32_C1_gt0 hS.
have /andP [hm0 hmn] := hm.
have hn : (0 : R) < n%:R by rewrite ltr0n (leq_trans hm0 hmn).
have hA : 0 <= (16 * n%:R + 6) * Lam ^+ 2 + 16 :> R.
  apply: addr_ge0 => //; apply: mulr_ge0; last exact: sqr_ge0.
  by apply: addr_ge0 => //; apply: mulr_ge0 => //; exact: ler0n.
have h2n : (0 : R) < 2 * n%:R by rewrite mulr_gt0.
rewrite /dgpr_upper_entropy_constant; apply: (lt_le_trans h2n).
by rewrite lerDl; exact: mulr_ge0 (ltW hC1) hA.
Qed.

Section UpperEntropyLemma32.
Local Notation B := (dgpr_heat_B hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation HI := (hom_inner BX hCY heX).
Variable DB : TX -> X -> Hom X Y.
Hypothesis hDB : forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).
Variable C1 : R.
Hypothesis hC1 : 0 <= C1.
Hypothesis hI32 : forall t, 0 <= t < T ->
  (dgpr_fisher_information hS t <=
    ((n - m)%N%:R * gamma / (2 * (T - t)) + n%:R / 2 * dgpr_lemma31_m delta T gamma t)%:E +
    C1%:E * measure_upper_integral LL
      (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))))%E.

(** Source for [dgpr_upper_entropy_conditional]: DPGPR 2026, (4.1), and
    blueprint lem:upper_entropy, with the constant
    C = 2n + C1 ((16 n + 6) Λ² + 16) of [dgpr_lemma_3_2_conditional],
    under its hypotheses [hDB] and [hI32]; the Gaussian decay of ρ log q
    and ρ |B|² is lem:regularity. *)
Theorem dgpr_upper_entropy_conditional (tau : R) : 0 <= tau < T ->
  dgpr_entropy_tilde hS tau <=
    - (2^-1 * m%:R * gamma * LOG T) +
    (2 * n%:R + C1 * ((16 * n%:R + 6) * Lam ^+ 2 + 16)) * gamma *
      (1 + LOG ((1 + Num.sqrt T * delta) / gamma)).
Proof.
apply: dgpr_upper_entropy_of => s hs.
exact: (dgpr_lemma_3_2_conditional hDB (dgpr_regularity_entropy_gaussian hS)
  (dgpr_regularity_B2_gaussian hS) hC1 hI32 hs).
Qed.
End UpperEntropyLemma32.

End UpperEntropy.

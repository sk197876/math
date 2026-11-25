(** De Philippis, Gennaioli, Pigati and Rindler (2026), Lemma 3.1;
    blueprint dgpr_blueprint.tex, lem:DGPR31:
      ∫_0^T ∫ rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2) dL^n dL^1 t
        <= C gamma (1 + log((1 + T^(1/2) delta)/gamma)),
    with C = (16 n + 6) Lambda^2 + 16.

    The proof follows the blueprint: J(t) = ∫ rho_t log q_t and
    K(t) = ∫ rho_t |B_t|^2 are of class 1 on R ∩ {t : t < T} with
    derivatives ∫ H(rho log q)_t and ∫ H(rho |B|^2)_t (DgprHeatIntegral.v);
    at each time the integrand is bounded as in DgprLemma31Main.v; the
    fundamental theorem of calculus on [0,tau], Jensen's inequality
    (eq:31:J), the bound K <= Lambda^2 gamma and (eq:31:min) bound the
    integrals over [0,tau] (DgprTimeIntegrals.v, DgprEntropyBound.v);
    Lebesgue's increasing convergence theorem passes to [0,T).

    The outer integral is Federer's upper integral over the set [0,T)
    (2.4.10); the inner one is the upper integral over R^n (2.4.2). The
    field DB of space differentials of B is any field with the values of
    D B_t(x), and |DB_t(x)|^2 is the sum of |D B_t(x)(eps_i)|^2. The
    Gaussian decay before T of rho log q and of rho |B|^2 (lem:regularity
    with lem:classes(cl:product)) are the hypotheses [hJgauss] and
    [hKgauss] of the section. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates ScalarInnerProduct ProductInner TensorUP Bilinear
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralBounds SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP
  EuclideanLebesgueDimensions LebesgueScalarMeasure ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprHomNorms DgprDifferentialCalculus DgprHeatJets DgprStanding DgprHeatObjects
  DgprIdentities DgprFunctionals DgprIdentitiesSmooth DgprMeasureComparison DgprLemma31 DgprGrowthClasses
  DgprParameterIntegralSmooth DgprHeatIntegral DgprLemma31Main DgprTimeIntegrals DgprEntropyBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Lemma31Final.
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
Local Notation HI := (hom_inner BX hCY heX).
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
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation S := (dgpr_heat_S hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation LOG := (@RealExponential.logarithm R).

Variable DB : TX -> X -> Hom X Y.
Hypothesis hDB : forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).
Hypothesis hJgauss : dgpr_gaussian_decay_before hA T (fun p : TX => rho p * LOG (Q p)).
Hypothesis hKgauss : dgpr_gaussian_decay_before hA T (fun p : TX => rho p * HI (B p) (B p)).

(** Source for [dgpr_lemma31_entropy_bounds]: blueprint proof of
    lem:DGPR31, (eq:31:J): for t < T,
    gamma log(gamma / (1 + (T - t)^(1/2) delta)) <= ∫ rho_t log q_t <= 0,
    by Jensen's inequality (DgprEntropyBound.v) with lem:identities(mass)
    and rho <= U <= S. *)
Lemma dgpr_lemma31_entropy_bounds (t j : R) : t < T ->
  is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * LOG (Q (t, x)))) j%:E ->
  gamma * LOG (gamma / (1 + Num.sqrt (T - t) * delta)) <= j <= 0.
Proof.
move=> ht hj.
have hg := dgpr_standing_gamma hS.
have hd0 : 0 <= delta.
  have h := measure_nonnegative (dgpr_standing_ups_measure hS) setT.
  by rewrite (dgpr_standing_ups_mass hS) lee_fin in h.
have [_ _ hSi hri] := dgpr_identities_mass hS ht.
have hM : 0 < 1 + Num.sqrt (T - t) * delta.
  by apply: (lt_le_trans ltr01); rewrite lerDl mulr_ge0 ?sqrtr_ge0.
have hpos x : 0 < rho (t, x) <= S (t, x).
  have [[hr0 hrU] hUS _ _ _] := dgpr_identities_bounds_full hS x ht.
  by rewrite hr0 (le_trans hrU hUS).
exact: (@dgpr_entropy_jensen_lebesgue R n (fun x => rho (t, x)) (fun x => S (t, x)) gamma
  (1 + Num.sqrt (T - t) * delta) j hg hM hpos hri hSi hj).
Qed.

(** Source for [dgpr_lemma31_majorant]: blueprint proof of lem:DGPR31:
    there is a function g on R ∩ {t : t < T} with 0 <= g(t), with the
    upper integral of rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2) at most
    g(t), and with ∫_0^tau g <= C gamma (1 + log((1 + T^(1/2) delta)/gamma))
    for 0 <= tau < T, where C = (16 n + 6) Lambda^2 + 16; namely
    g = (1 + 4n) K' + (16 n + 6) Lambda^2 J' + 4 m. *)
Theorem dgpr_lemma31_majorant : exists g : R -> R,
  (forall t, t < T -> (0 <= g t) /\
     (measure_upper_integral LL (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x)))
       <= (g t)%:E)%E) /\
  (forall tau, 0 <= tau < T -> exists G : R,
     is_measure_subset_integral L1 `[0, tau] (real_total_integrand g) G%:E /\
     G <= ((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma))).
Proof.
have hT := dgpr_standing_T hS.
have hg := dgpr_standing_gamma hS.
have hL0 : 0 <= Lam := ltW (dgpr_standing_Lambda hS).
have hd0 : 0 <= delta.
  have h := measure_nonnegative (dgpr_standing_ups_measure hS) setT.
  by rewrite (dgpr_standing_ups_mass hS) lee_fin in h.
have hg1 : gamma <= 1.
  have h := dgpr_standing_mu0_le hS setT.
  by rewrite (dgpr_standing_mu0_mass hS) (dgpr_standing_mu_mass hS) lee_fin in h.
have hHJ := fun t x (ht : t < T) => dgpr_lemma31_heat_J hS x ht.
have hHK := fun t x (ht : t < T) => dgpr_lemma31_heat_K hDB x ht.
have [IJ [HJ [hIJ hHJi hcJ]]] := dgpr_heat_integral hJgauss hHJ.
have [IK [HK [hIK hHKi hcK]]] := dgpr_heat_integral hKgauss hHK.
set c1 : R := 1 + 4 * n%:R.
set c2 : R := (16 * n%:R + 6) * Lam ^+ 2.
have hc1 : 0 <= c1 by rewrite /c1 addr_ge0 // mulr_ge0.
have hc2 : 0 <= c2 by rewrite /c2 mulr_ge0 ?sqr_ge0 // addr_ge0 // mulr_ge0.
pose g (t : R) : R := c1 * HK t + c2 * HJ t + 4 * dgpr_lemma31_m delta T gamma t.
have hslice t : t < T -> 0 <= g t /\
    (measure_upper_integral LL (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x)))
      <= (g t)%:E)%E.
  by move=> ht; exact: (dgpr_lemma31_time_slice hDB ht (hHJi t ht) (hHKi t ht)).
set Lb := LOG ((1 + Num.sqrt T * delta) / gamma).
have hJ0 : - IJ 0 <= gamma * Lb.
  have /andP [h _] := dgpr_lemma31_entropy_bounds hT (hIJ 0 hT).
  rewrite subr0 in h.
  have hM : 0 < 1 + Num.sqrt T * delta.
    by apply: (lt_le_trans ltr01); rewrite lerDl mulr_ge0 ?sqrtr_ge0.
  have e : LOG (gamma / (1 + Num.sqrt T * delta)) = - Lb.
    by rewrite /Lb -invf_div real_logarithm_inverse // divr_gt0.
  by rewrite e mulrN in h; rewrite lerNl.
have hK0 : 0 <= IK 0.
  by have /andP [h _] := dgpr_lemma31_K_bound hT (hIK 0 hT).
have hlog : LOG (1 + Num.sqrt T * delta / gamma) <= Lb.
  have hsd : 0 <= Num.sqrt T * delta by apply: mulr_ge0 => //; exact: sqrtr_ge0.
  have hp1 : 0 < 1 + Num.sqrt T * delta / gamma.
    apply: (lt_le_trans ltr01); rewrite lerDl.
    by apply: mulr_ge0 => //; rewrite invr_ge0; exact: ltW.
  have hp2 : 0 < (1 + Num.sqrt T * delta) / gamma.
    by apply: divr_gt0 => //; apply: (lt_le_trans ltr01); rewrite lerDl.
  rewrite /Lb real_logarithm_order // mulrDl mul1r lerD2r.
  by rewrite -[1 in X in X <= _]invr1 lef_pV2 // posrE.
exists g; split; first exact: hslice.
move=> tau htau; have /andP [h0 hτ] := htau.
have hFJ := dgpr_before_ftc h0 hτ hcJ.
have hFK := dgpr_before_ftc h0 hτ hcK.
have [Gm [hGm hGmb]] := dgpr_time_min_integral hT hg hd0 htau.
have hsum := dgpr_segment_integral_add
  (dgpr_segment_integral_add (dgpr_segment_integral_scale c1 hFK) (dgpr_segment_integral_scale c2 hFJ))
  (dgpr_segment_integral_scale 4 hGm).
exists (c1 * (IK tau - IK 0) + c2 * (IJ tau - IJ 0) + 4 * Gm); split; first exact: hsum.
have hKt : IK tau <= Lam ^+ 2 * gamma.
  by have /andP [_ h] := dgpr_lemma31_K_bound hτ (hIK tau hτ).
have hJt : IJ tau <= 0.
  by have /andP [_ h] := dgpr_lemma31_entropy_bounds hτ (hIJ tau hτ).
have h1 : c1 * (IK tau - IK 0) <= c1 * (Lam ^+ 2 * gamma).
  by apply: ler_wpM2l => //; lra.
have h2 : c2 * (IJ tau - IJ 0) <= c2 * (gamma * Lb).
  by apply: ler_wpM2l => //; lra.
have h3 : 4 * Gm <= 16 * (gamma * Lb).
  have : Gm <= 4 * (gamma * Lb).
    apply: le_trans hGmb _; rewrite -mulrA ler_pM2l //.
    by apply: ler_wpM2l => //; exact: ltW.
  lra.
have h4 : c1 * (Lam ^+ 2 * gamma) <= (c2 + 16) * gamma.
  rewrite /c1 /c2 mulrA; apply: ler_wpM2r; first exact: ltW.
  have hn0 : 0 <= n%:R :> R := ler0n _ _.
  have hl2 : 0 <= Lam ^+ 2 := sqr_ge0 _.
  nra.
have e : ((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma * (1 + Lb) =
    (c2 + 16) * gamma + c2 * (gamma * Lb) + 16 * (gamma * Lb).
  by rewrite /c2; ring.
rewrite e; lra.
Qed.

(** Source for [dgpr_lemma_3_1_conditional]: DPGPR 2026, Lemma 3.1, and
    blueprint lem:DGPR31, with C = (16 n + 6) Lambda^2 + 16, under the
    hypotheses [hJgauss] and [hKgauss] of the section: Lebesgue's
    increasing convergence theorem (Federer 2.4.7) applied to
    [dgpr_lemma31_majorant] on [0, tau] as tau -> T-. *)
Theorem dgpr_lemma_3_1_conditional :
  (measure_subset_upper_integral L1 [set t : R | (0 <= t < T)%R]
     (partial_function_total (fun t : R => measure_upper_integral LL
        (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x)))))
   <= (((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma *
        (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E.
Proof.
have [g [hs hG]] := dgpr_lemma31_majorant.
apply: (@dgpr_before_upper_integral R T _ _ g (dgpr_standing_T hS)).
- by move=> t /andP [_ ht]; exact: (hs t ht).2.
- by move=> t /andP [_ ht]; exact: (hs t ht).1.
- exact: hG.
Qed.

End Lemma31Final.

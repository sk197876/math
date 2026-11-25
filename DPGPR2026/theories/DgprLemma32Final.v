(** De Philippis, Gennaioli, Pigati and Rindler (2026), Lemma 3.2;
    blueprint dgpr_blueprint.tex, lem:DGPR32, last step of the proof:
    integration of eq:32:I over [0,tau]. With a constant C1 >= 0 for
    which eq:32:I holds and the constant C = (16 n + 6) Lambda^2 + 16 of
    lem:DGPR31,
      ∫_0^tau (I(rho_t) - (n - m) gamma / (2 (T - t))) dL^1 t
        <= (2n + C1 C) gamma (1 + log((1 + T^(1/2) delta)/gamma))
    for 0 <= tau < T.

    The integral over [0,tau] is Federer's upper integral over the
    segment (2.4.10). The estimate eq:32:I at a fixed time, with any
    constant C1 >= 0, is the hypothesis [hI32] of the section; the
    majorant of lem:DGPR31
    (DgprLemma31Final.v) and (eq:31:min) (DgprTimeIntegrals.v) bound the
    integral of its right side. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates ScalarInnerProduct ProductInner TensorUP Bilinear
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralMonotone MeasureIntegralGraphEquivalence PartialExtendedOrderLoci
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP
  EuclideanLebesgueDimensions LebesgueScalarMeasure ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprHomNorms DgprDifferentialCalculus DgprHeatJets DgprStanding DgprHeatObjects
  DgprIdentities DgprFunctionals DgprIdentitiesSmooth DgprMeasureComparison DgprLemma31 DgprGrowthClasses
  DgprParameterIntegralSmooth DgprHeatIntegral DgprLemma31Main DgprTimeIntegrals DgprEntropyBound
  DgprLemma31Final.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section SegmentUpper.
Variable R : realType.
Local Notation L1 := (@lebesgue_scalar_measure R).

(** Source for [dgpr_segment_upper_integral_le]: Federer 2.4.2-2.4.4 and
    2.4.10, pp. 81-85: if phi <= g on [a,b] and g has the integral G over
    [a,b], then the upper integral of phi over [a,b] is at most G. *)
Lemma dgpr_segment_upper_integral_le (a b G : R) (phi : R -> \bar R) (g : R -> R) :
  (forall t, a <= t <= b -> (phi t <= (g t)%:E)%E) ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g) G%:E ->
  (measure_subset_upper_integral L1 `[a, b] (partial_function_total phi) <= G%:E)%E.
Proof.
move=> hphi /dgpr_segment_integralE hG.
have hm := lebesgue_scalar_is_measure R.
have eG := @measure_upper_integral_unique R R L1 _ _ G%:E
  (measure_upper_integral_specification _ _) hG.2.1.
rewrite -eG /measure_subset_upper_integral.
apply: measure_upper_integral_monotone => //.
apply: (@measure_almost_everywhere_mono R R L1 hm setT _ _ (measure_almost_everywhere_true hm)) => x _.
case: (boolP (a <= x <= b)) => hx.
- exists (phi x), (g x)%:E; split; [|split].
  + by apply/partial_function_zero_extension_graph; left; split => //; rewrite in_itv.
  + by apply/real_total_integrand_graph; rewrite hx.
  + exact: hphi.
- exists 0%E, 0%E; split; [|split].
  + apply/partial_function_zero_extension_graph; right; split => //.
    by rewrite /= in_itv /= (negbTE hx).
  + by apply/real_total_integrand_graph; rewrite (negbTE hx).
  + exact: lexx.
Qed.
End SegmentUpper.

Section Lemma32Final.
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
Local Notation B := (dgpr_heat_B hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation LOG := (@RealExponential.logarithm R).

Variable DB : TX -> X -> Hom X Y.
Hypothesis hDB : forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).
Hypothesis hJgauss : dgpr_gaussian_decay_before hA T (fun p : TX => rho p * LOG (Q p)).
Hypothesis hKgauss : dgpr_gaussian_decay_before hA T (fun p : TX => rho p * HI (B p) (B p)).

(** The estimate eq:32:I at a fixed time, with a nonnegative constant
    C1; [dgpr_lemma32_fixed_time] (DgprLemma32Pointwise.v) proves it with
    C1 = (2n + 1)(32 Lambda / (3 lambda^2))^2 + 32 / (3 lambda^2). *)
Variable C1 : R.
Hypothesis hC1 : 0 <= C1.
Hypothesis hI32 : forall t, 0 <= t < T ->
  (dgpr_fisher_information hS t <=
    ((n - m)%N%:R * gamma / (2 * (T - t)) + n%:R / 2 * dgpr_lemma31_m delta T gamma t)%:E +
    C1%:E * measure_upper_integral LL
      (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))))%E.

(** Source for [dgpr_lemma32_log_bound]: log(1 + T^(1/2) delta / gamma)
    <= log((1 + T^(1/2) delta)/gamma), since gamma <= 1; second
    inequality of (eq:31:min). *)
Lemma dgpr_lemma32_log_bound :
  LOG (1 + Num.sqrt T * delta / gamma) <= LOG ((1 + Num.sqrt T * delta) / gamma).
Proof.
have hg := dgpr_standing_gamma hS.
have hd0 : 0 <= delta.
  have h := measure_nonnegative (dgpr_standing_ups_measure hS) setT.
  by rewrite (dgpr_standing_ups_mass hS) lee_fin in h.
have hg1 : gamma <= 1.
  have h := dgpr_standing_mu0_le hS setT.
  by rewrite (dgpr_standing_mu0_mass hS) (dgpr_standing_mu_mass hS) lee_fin in h.
have hsd : 0 <= Num.sqrt T * delta by apply: mulr_ge0 => //; exact: sqrtr_ge0.
have hp1 : 0 < 1 + Num.sqrt T * delta / gamma.
  apply: (lt_le_trans ltr01); rewrite lerDl.
  by apply: mulr_ge0 => //; rewrite invr_ge0; exact: ltW.
have hp2 : 0 < (1 + Num.sqrt T * delta) / gamma.
  by apply: divr_gt0 => //; apply: (lt_le_trans ltr01); rewrite lerDl.
rewrite real_logarithm_order // mulrDl mul1r lerD2r.
by rewrite -[1 in X in X <= _]invr1 lef_pV2 // posrE.
Qed.

(** Source for [dgpr_lemma_3_2_conditional]: DPGPR 2026, Lemma 3.2, and
    blueprint lem:DGPR32, last step of the proof: integration of eq:32:I
    (hypothesis [hI32], with the constant C1) over [0,tau], with
    (eq:31:min) and lem:DGPR31 ([dgpr_lemma31_majorant]). *)
Theorem dgpr_lemma_3_2_conditional (tau : R) : 0 <= tau < T ->
  (measure_subset_upper_integral L1 `[0%R, tau]
     (partial_function_total (fun t : R =>
        dgpr_fisher_information hS t - ((n - m)%N%:R * gamma / (2 * (T - t)))%:E))
   <= ((2 * n%:R + C1 * ((16 * n%:R + 6) * Lam ^+ 2 + 16)) * gamma *
        (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E.
Proof.
move=> htau; have /andP [h0 hτ] := htau.
have hT := dgpr_standing_T hS.
have hg := dgpr_standing_gamma hS.
have hd0 : 0 <= delta.
  have h := measure_nonnegative (dgpr_standing_ups_measure hS) setT.
  by rewrite (dgpr_standing_ups_mass hS) lee_fin in h.
have [g [hs hG]] := dgpr_lemma31_majorant hDB hJgauss hKgauss.
have [G [hGi hGb]] := hG tau htau.
have [Gm [hGm hGmb]] := dgpr_time_min_integral hT hg hd0 htau.
have hG2 := dgpr_segment_integral_add (dgpr_segment_integral_scale (n%:R / 2) hGm)
  (dgpr_segment_integral_scale C1 hGi).
apply: le_trans (dgpr_segment_upper_integral_le _ hG2) _.
  move=> t /andP [ht0 htt].
  have htT : t < T := le_lt_trans htt hτ.
  have hI := hI32 (introT andP (conj ht0 htT)).
  have [_ hUI] := hs t htT.
  set c := (n - m)%N%:R * gamma / (2 * (T - t)).
  set a := n%:R / 2 * dgpr_lemma31_m delta T gamma t.
  have h1 : (C1%:E * measure_upper_integral LL
      (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))) <=
      (C1 * g t)%:E)%E.
    by rewrite EFinM; apply: lee_wpmul2l => //; rewrite lee_fin.
  have h2 := le_trans hI (leeD (lexx (c + a)%:E) h1).
  have h3 := leeB h2 (lexx c%:E).
  have e : ((c + a)%:E + (C1 * g t)%:E - c%:E)%E = (a + C1 * g t)%:E.
    by rewrite -[((c + a)%:E + _)%E]EFinD -EFinB; congr (_%:E); ring.
  by rewrite e in h3.
rewrite lee_fin.
have hlog := dgpr_lemma32_log_bound.
set Lb := LOG ((1 + Num.sqrt T * delta) / gamma).
have hn0 : 0 <= n%:R :> R := ler0n _ _.
have hGm' : Gm <= 4 * gamma * Lb.
  apply: le_trans hGmb _.
  by apply: ler_wpM2l => //; rewrite mulr_ge0 // ltW.
have hGG : C1 * G <= C1 * (((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma * (1 + Lb)).
  exact: ler_wpM2l.
have hnG : n%:R / 2 * Gm <= n%:R / 2 * (4 * gamma * Lb).
  by apply: ler_wpM2l => //; rewrite divr_ge0.
have hng : 0 <= n%:R * gamma by rewrite mulr_ge0 // ltW.
have e : (2 * n%:R + C1 * ((16 * n%:R + 6) * Lam ^+ 2 + 16)) * gamma * (1 + Lb) =
    2 * (n%:R * gamma) + n%:R / 2 * (4 * gamma * Lb) +
    C1 * (((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma * (1 + Lb)).
  by field.
rewrite e; lra.
Qed.

End Lemma32Final.

(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Theorem 1.1; blueprint dgpr_blueprint.tex, lem:compact_case, for the
    data of mr:hypotheses_main.

    Let C0 = [dgpr_upper_entropy_constant n λ Λ] be the constant of
    lem:upper_entropy and C = [dgpr_compact_case_constant n C0]
    (DgprCompactCase.v); C depends only on n, λ and Λ. Whenever Y is a
    finite dimensional inner product space, the data of
    mr:hypotheses_main are given with these λ and Λ, and
    μ(R^n ∖ B(0, r_0)) = 0 for some 0 < r_0 < ∞, then
        μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n)
    ([dgpr_compact_case_general], the proposition
    [dgpr_compact_case_inequality] of DgprMainHypothesesCompact.v).

    The proof is that of the blueprint. If a = μ(R^n) = 0 there is
    nothing to prove. Otherwise the dual density dΥ of ‖Υ‖
    ([dgpr_dual_density], DgprDualDensity.v) and an element A_0 ∈ K give
    the hypotheses (S) for the normalised data a^{-1} μ, the extension of
    X by A_0, a^{-1} Υ, a^{-1} ‖Υ‖ and δ = a^{-1} ‖Υ‖(R^n)
    ([dgpr_main_standing], DgprMainToStanding.v). By lem:inner
    ([dgpr_inner_approximation]) there is a compact k rectifiable set
    E ⊆ M with μ(R^n ∖ E) < a/2; hence γ = a^{-1} μ(E) > 1/2. Since μ is
    absolutely continuous with respect to H^k ⌞ M,
    0 < H^k(E) ≤ H^k(M) < ∞. With μ_0 = a^{-1} μ ⌞ E
    ([dgpr_standing_restrict]), [dgpr_compact_case_standing] gives
    1 ≤ C H^k(E)^{1/k} δ, that is, a ≤ C H^k(E)^{1/k} ‖Υ‖(R^n), and
    H^k(E)^{1/k} ≤ H^k(M)^{1/k}. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner InnerConvex
  InnerMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP
  MeasureRestriction MeasureSplit MeasureDensity MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP RadonMeasureUP FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationUP SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  NormDifferentialUP HausdorffMeasure RectifiableSetUP TopologicalBorel RealPower MeasureScaleIntegral.
From DPGPR Require Import DgprStanding DgprMainHypotheses DgprMainHypothesesCompact DgprUpperEntropy DgprCompactCase
  DgprInnerApproximation DgprDualDensity DgprMainToStanding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactCaseGeneral.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).

(** Source for [dgpr_compact_case_general]: DPGPR 2026, proof of
    Theorem 1.1, and blueprint lem:compact_case: for 0 < λ and 0 < Λ,
    the constant C = [dgpr_compact_case_constant n C0] with
    C0 = [dgpr_upper_entropy_constant n λ Λ], which depends only on n, λ
    and Λ, satisfies μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n) whenever the data
    of mr:hypotheses_main are given and μ(R^n ∖ B(0, r_0)) = 0 for some
    0 < r_0 < ∞. *)
Theorem dgpr_compact_case_general (lam Lam : R) : 0 < lam -> 0 < Lam ->
  dgpr_compact_case_inequality hk lam Lam
    (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam)).
Proof.
move=> _ _ Y CY hCY d eY E ev hE K M theta Xf Ups ups hH [r0 [hr0 hsupp]].
set C := dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam).
set mu := dgpr_main_measure k M theta.
have heY := dgpr_main_Y_basis hH.
have htheta := dgpr_main_theta_nonnegative hH.
have hsum := dgpr_main_theta_summable hH.
have hmu : is_measure mu := dgpr_main_measure_is_measure k htheta.
have [a ha] : exists a : R, mu setT = a%:E := dgpr_main_measure_finite htheta hsum.
have ha0 : 0 <= a by rewrite -lee_fin -ha; exact: measure_nonnegative hmu setT.
have hups := dgpr_main_ups_measure hH.
set u := fine (ups setT).
have hupsfin : ups setT = u%:E.
  by rewrite /u fineK // ge0_fin_numE ?(measure_nonnegative hups) // (dgpr_main_ups_finite hH).
have hu0 : 0 <= u by rewrite -lee_fin -hupsfin; exact: measure_nonnegative hups setT.
have hC0 : 0 < C := dgpr_compact_case_constant_gt0 n _.
have hP0 : 0 <= real_power (fine (HK M)) (k%:R)^-1 := real_power_nonnegative _ _.
rewrite -/mu ha hupsfin -EFinM lee_fin.
have [->|ha1] := eqVneq a 0.
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ltW.
have hapos : 0 < a by rewrite lt_neqAle eq_sym ha1 ha0.
have [A0 hA0] := dgpr_main_K_nonempty hH.
have [dups [hdm hdb hda]] := dgpr_dual_density heY hups (dgpr_main_ups_radon hH)
  (dgpr_main_ups_gauge hH).
have hS := dgpr_main_standing hH ha hapos hr0 hsupp hA0 hdm hdb hda.
have ha2 : 0 < a / 2 by rewrite divr_gt0.
have [Ec [hEM hEc hEr hEeps]] := dgpr_inner_approximation (dgpr_main_M_borel hH)
  (dgpr_main_M_rectifiable hH) (dgpr_main_M_finite hH) htheta hsum ha2.
have hEeps' : (mu (~` Ec) < (a / 2)%:E)%E := hEeps.
have hcov : (mu setT <= mu Ec + mu (~` Ec))%E.
  apply: (measure_binary_cover hmu) => x _.
  by case: (pselect (Ec x)) => hx; [left|right].
have hEle : (mu Ec <= a%:E)%E by rewrite -ha; exact: (measure_mono hmu (subsetT Ec)).
have hEfin : mu Ec = (fine (mu Ec))%:E.
  rewrite fineK // ge0_fin_numE ?(measure_nonnegative hmu) //.
  exact: le_lt_trans hEle (ltry a).
have hCfin : mu (~` Ec) = (fine (mu (~` Ec)))%:E.
  rewrite fineK // ge0_fin_numE ?(measure_nonnegative hmu) //.
  exact: lt_trans hEeps' (ltry _).
set g := fine (mu Ec).
set w := fine (mu (~` Ec)).
have hw : w < a / 2 by rewrite -lte_fin -hCfin.
have hg : a <= g + w by rewrite -lee_fin EFinD -hEfin -hCfin -ha.
have hga : a / 2 < g by lra.
set gam := a^-1 * g.
have hgam : 2^-1 < gam.
  by rewrite /gam -(ltr_pM2l hapos) mulrA mulfV ?gt_eqF // mul1r.
have hgam0 : 0 < gam by apply: lt_trans hgam; rewrite invr_gt0.
have hmun : measure_scale a^-1 mu Ec = gam%:E by rewrite /measure_scale hEfin -EFinM.
have hS' := dgpr_standing_restrict hS hmun hgam0.
have hHm := hausdorff_measure_is_measure RnM k.
have hHE : (HK Ec <= HK M)%E := measure_mono hHm hEM.
have hHMfin := dgpr_main_M_finite hH.
have hmuE : (0 < mu Ec)%E by rewrite hEfin lte_fin; exact: lt_trans ha2 hga.
have hHE0 : (0 < HK Ec)%E := dgpr_main_measure_hausdorff hmuE.
have hhE : HK Ec = (fine (HK Ec))%:E.
  rewrite fineK // ge0_fin_numE ?(measure_nonnegative hHm) //.
  exact: le_lt_trans hHE hHMfin.
have hhM : HK M = (fine (HK M))%:E.
  by rewrite fineK // ge0_fin_numE ?(measure_nonnegative hHm).
set h := fine (HK Ec).
have hh0 : 0 < h by rewrite -lte_fin -hhE.
have hhle : h <= fine (HK M) by rewrite -lee_fin -hhE -hhM.
have hmain := dgpr_compact_case_standing (erefl (measure_restrict (measure_scale a^-1 mu) Ec))
  hS' hEc hEr hhE hh0 hgam.
have hk0 : 0 < (k%:R : R)^-1 by rewrite invr_gt0 ltr0n; case/andP: hk.
have hpow : real_power h (k%:R)^-1 <= real_power (fine (HK M)) (k%:R)^-1 :=
  real_power_monotone (ltW hh0) hhle hk0.
have e : a * (C * real_power h (k%:R)^-1 * (a^-1 * u)) = C * real_power h (k%:R)^-1 * u.
  by rewrite mulrCA mulVKf.
apply: (@le_trans _ _ (C * real_power h (k%:R)^-1 * u)).
  by rewrite -e -{1}(mulr1 a) (ler_pM2l hapos).
apply: (ler_wpM2r hu0); exact: (ler_wpM2l (ltW hC0) hpow).
Qed.

End CompactCaseGeneral.

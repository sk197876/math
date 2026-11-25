(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.3),
    (3.4) and the identity before (3.12); blueprint dgpr_blueprint.tex,
    lem:identities: the identities of the heated objects of
    def:heat_objects under the standing hypotheses (S).

    The names follow the items of lem:identities: (heat) is
    [dgpr_identities_heat_extensions] here and [dgpr_identities_heat] in
    DgprHeatCalculus.v, (mass) is [dgpr_identities_mass], (bounds) is
    [dgpr_identities_bounds], and (sv) is [dgpr_identities_sv]. The items
    (spt), (div) and (divB) are in DgprIdentitiesDivergence.v. The
    inequality rho <= U of (bounds) is [dgpr_identities_rho_le_U]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  CompleteMetricUP VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralComparison SummableRealFunctionUP
  SummableRealArithmetic RadonMeasureUP EuclideanLebesgueDimensions ScalarNormMetricCompleteness
  LocalUniquenessExample SmoothFunctionSpaceUP SmoothTestSpaces MeasureBasic MeasureDensity MeasureDensityUP
  MeasureChangeOfDensity PartialDensityProduct PartialExtendedOrderLoci MeasureSubsetIntegral PartialZeroExtensionLaws
  ContinuousRealFunctional MeasureIntegralUniqueness MeasureIntegralBounds MeasureVectorIntegralUP
  HomSpaceNormTopology InnerConvex MeasureIntegralGraphEquivalence.
From DPGPR Require Import DgprSingularValue DgprHeatKernel DgprHeatExtension DgprHeatExtensionMass
  DgprHeatSemiconvex DgprHeatExtensionBounds DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects
  DgprBarycentre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_ratio_bound]: elementary algebra used in the proof
    of lem:identities(bounds): if 0 < a, 0 < c and c b <= a, then
    a^(-1) b <= c^(-1). *)
Lemma dgpr_ratio_bound (R : realType) (a b c : R) : 0 < a -> 0 < c -> c * b <= a -> a^-1 * b <= c^-1.
Proof.
move=> ha hc h.
by rewrite ler_pdivrMl // ler_pdivlMr // mulrC.
Qed.

Section Identities.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
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
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
Local Notation hHc := (@dgpr_hom_space_complete R n Y CY hCY d eY heY).
Local Notation hDc := (@dgpr_dual_space_complete R Y CY hCY d eY heY).
Local Notation hHs := (@dgpr_hom_space_separable R n Y CY hCY d eY heY).
Local Notation hDs := (@dgpr_dual_space_separable R Y CY hCY d eY heY).
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
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOups := (radon_open_measurable (dgpr_standing_ups_radon hS)).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMups := (dgpr_standing_ups_mass hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation Psi := (dgpr_heat_Psi hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation kappa := (dgpr_heat_kappa hS).

(** Source for [dgpr_one_bound1]: |1| <= 1, the bound of def:heat for
    the constant function 1. *)
Lemma dgpr_one_bound1 (y : X) : `|(1 : R^o)| <= 1.
Proof. by rewrite normr1. Qed.

(** Source for [dgpr_standing_mu0_support]: mu0(R^n - B(0,r0)) <=
    mu(R^n - B(0,r0)) = 0 by (S); blueprint mr:standing. *)
Lemma dgpr_standing_mu0_support : measure_almost_everywhere mu0 [set y | N y <= r0].
Proof.
rewrite /measure_almost_everywhere; apply/eqP; rewrite eq_le (measure_nonnegative hmu0) andbT.
have h := dgpr_standing_mu0_le hS (~` [set y | N y <= r0]).
by move: h; rewrite (dgpr_standing_mu_support hS).
Qed.

(** Source for [dgpr_identities_heat_extensions]: blueprint
    lem:identities(heat), first five equations, and DPGPR 2026, (3.3):
    H U = H W = H R = H Psi = H rho = 0 on Omega_T, since each is
    [(t,x) |-> u(T - t, x)] for a heat extension u (DgprBackwardHeat.v). *)
Theorem dgpr_identities_heat_extensions (t : R) (x : X) : t < T ->
  [/\ dgpr_heat_operator A1 U t x 0, dgpr_heat_operator NH W t x 0,
      dgpr_heat_operator A1 Rr t x 0, dgpr_heat_operator ND Psi t x 0 &
      dgpr_heat_operator A1 rho t x 0].
Proof.
move=> ht; split.
- exact: (dgpr_backward_heat_operator hmu hZ1 hOmu hMmu hsep1 (dgpr_one_measurable hmu) dgpr_one_bound1 x ht).
- exact: (dgpr_backward_heat_operator hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
    (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) x ht).
- exact: (dgpr_backward_heat_operator hups hZ1 hOups hMups hsep1 (dgpr_one_measurable hups) dgpr_one_bound1 x ht).
- exact: (dgpr_backward_heat_operator hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
    (dgpr_standing_dups_bound hS) x ht).
- exact: (dgpr_backward_heat_operator hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0) dgpr_one_bound1 x ht).
Qed.

(** Source for [dgpr_identities_mass]: blueprint lem:identities(mass)
    and DPGPR 2026, section 3: for t < T the integrals of U_t, R_t, S_t
    and rho_t with respect to L^n are 1, delta, 1 + (T - t)^(1/2) delta
    and gamma, by lem:heat_extension(4) (Federer 2.6.2) and 2.4.4. *)
Theorem dgpr_identities_mass (t : R) : t < T ->
  [/\ is_measure_integral LL (real_total_integrand (fun x => U (t, x))) 1%:E,
      is_measure_integral LL (real_total_integrand (fun x => Rr (t, x))) delta%:E,
      is_measure_integral LL (real_total_integrand (fun x => S (t, x))) (1 + Num.sqrt (T - t) * delta)%:E &
      is_measure_integral LL (real_total_integrand (fun x => rho (t, x))) gamma%:E].
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have hb1 := dgpr_constant_integral hmu hMmu 1; rewrite mul1r in hb1.
have hb2 := dgpr_constant_integral hups hMups 1; rewrite mul1r in hb2.
have hb3 := dgpr_constant_integral hmu0 hMmu0 1; rewrite mul1r in hb3.
have hU : is_measure_integral LL (real_total_integrand (fun x => U (t, x))) 1%:E.
  exact: (dgpr_heat_extension_mass hmu hOmu hMmu (dgpr_one_measurable hmu) dgpr_one_bound1
    (fun _ => ler01) hs hb1).
have hR : is_measure_integral LL (real_total_integrand (fun x => Rr (t, x))) delta%:E.
  exact: (dgpr_heat_extension_mass hups hOups hMups (dgpr_one_measurable hups) dgpr_one_bound1
    (fun _ => ler01) hs hb2).
split => //.
- exact: (real_total_integral_add hLL hU (real_total_integral_scale hLL (Num.sqrt (T - t)) hR)).
- exact: (dgpr_heat_extension_mass hmu0 hOmu0 hMmu0 (dgpr_one_measurable hmu0) dgpr_one_bound1
    (fun _ => ler01) hs hb3).
Qed.

(** Source for [dgpr_identities_U_pos]: blueprint proof of
    lem:identities(bounds), U > 0 by lem:heat_extension(3); DPGPR 2026,
    section 3. *)
Lemma dgpr_identities_U_pos (t : R) (x : X) : t < T -> 0 < U (t, x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
exact: (dgpr_heat_extension_positive hmu hOmu hMmu (dgpr_standing_mu_support hS) ltr01 x hs).
Qed.

(** Source for [dgpr_identities_rho_pos]: blueprint proof of
    lem:identities(bounds), rho > 0 by lem:heat_extension(3), since
    mu0(R^n) = gamma > 0 and mu0 is carried by B(0,r0). *)
Lemma dgpr_identities_rho_pos (t : R) (x : X) : t < T -> 0 < rho (t, x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
exact: (dgpr_heat_extension_positive hmu0 hOmu0 hMmu0 dgpr_standing_mu0_support
  (dgpr_standing_gamma hS) x hs).
Qed.

(** Source for [dgpr_identities_R_ge0]: R(t,x) >= 0, since R(t,x) is the
    integral of the positive function [y |-> p_(T-t)(x-y)] with respect to
    ||Upsilon|| (Federer 2.4.4(5)); supporting blueprint
    lem:identities(bounds). *)
Lemma dgpr_identities_R_ge0 (t : R) (x : X) : t < T -> 0 <= Rr (t, x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have h1 := dgpr_unit_kernel_integral hups hOups hMups x hs.
have h0 := dgpr_constant_integral hups hMups 0; rewrite mul0r in h0.
rewrite -lee_fin; apply: (measure_integral_monotone hups h0 h1).
apply: (measure_almost_everywhere_mono hups _ (measure_almost_everywhere_true hups)) => y _.
exists 0%:E, (p (T - t) (x - y))%:E; split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
by rewrite lee_fin ltW // dgpr_kernel_gt0.
Qed.

(** Source for [dgpr_identities_Psi_bound]: blueprint
    lem:identities(div), ||Psi(t,x)|| <= R(t,x): by lem:heat_extension(2)
    with j = 0, ||Psi(t,x)|| is at most the integral of
    p_(T-t)(x-y) ||dUpsilon(y)|| d ||Upsilon|| y, and ||dUpsilon|| <= 1. *)
Theorem dgpr_identities_Psi_bound (t : R) (x : X) : t < T -> ND (Psi (t, x)) <= Rr (t, x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have h1 := dgpr_heat_extension_zero_bound hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
  (dgpr_standing_dups_bound hS) x hs.
apply: (le_trans h1).
have hn := dgpr_heat_norm_integral hups hOups hMups (dgpr_standing_dups_measurable hS)
  (dgpr_standing_dups_bound hS) x hs.
have hu := dgpr_unit_kernel_integral hups hOups hMups x hs.
rewrite -lee_fin; apply: (measure_integral_monotone hups hn hu).
apply: (measure_almost_everywhere_mono hups _ (measure_almost_everywhere_true hups)) => y _.
exists (p (T - t) (x - y) * ND (dups y))%:E, (p (T - t) (x - y))%:E.
split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin; apply: ler_piMr; first exact: (ltW (dgpr_kernel_gt0 _ hs)).
exact: (dgpr_standing_dups_bound hS y).
Qed.

(** Source for [dgpr_identities_U_le_S]: blueprint proof of
    lem:identities(bounds), U <= S by definition, since R >= 0. *)
Lemma dgpr_identities_U_le_S (t : R) (x : X) : t < T -> U (t, x) <= S (t, x).
Proof.
move=> ht; rewrite /dgpr_heat_S /= lerDl mulr_ge0 ?sqrtr_ge0 //.
exact: dgpr_identities_R_ge0.
Qed.

(** Source for [dgpr_identities_S_pos]: S > 0 on Omega_T, since
    0 < U <= S; blueprint proof of lem:identities(bounds). *)
Lemma dgpr_identities_S_pos (t : R) (x : X) : t < T -> 0 < S (t, x).
Proof.
move=> ht; exact: (lt_le_trans (dgpr_identities_U_pos x ht) (dgpr_identities_U_le_S x ht)).
Qed.

(** Source for [dgpr_identities_kappa_ge0]: kappa >= 0 on Omega_T;
    blueprint lem:identities(bounds). *)
Lemma dgpr_identities_kappa_ge0 (t : R) (x : X) : t < T -> 0 <= kappa (t, x).
Proof.
move=> ht; rewrite /dgpr_heat_kappa /=.
rewrite divr_ge0 ?dgpr_identities_R_ge0 // !mulr_ge0 ?sqrtr_ge0 //.
exact: (ltW (dgpr_identities_S_pos x ht)).
Qed.

(** Source for [dgpr_identities_eta_bound]: blueprint proof of
    lem:identities(bounds): (T - t)^(1/2) R <= S and ||Psi|| <= R give
    ||eta|| <= S^(-1) R <= (T - t)^(-1/2). *)
Theorem dgpr_identities_eta_bound (t : R) (x : X) : t < T -> ND (eta (t, x)) <= (Num.sqrt (T - t))^-1.
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have hS0 := dgpr_identities_S_pos x ht.
rewrite /dgpr_heat_eta /hom_norm (real_seminorm_scale hND.1) ger0_norm ?invr_ge0 ?(ltW hS0) //.
have hSi : 0 <= (S (t, x))^-1 by rewrite invr_ge0 ltW.
apply: (le_trans (ler_wpM2l hSi (dgpr_identities_Psi_bound x ht))).
apply: dgpr_ratio_bound => //; first by rewrite sqrtr_gt0.
rewrite /dgpr_heat_S /= lerDr.
exact: (ltW (dgpr_identities_U_pos x ht)).
Qed.

(** Source for [dgpr_identities_barycentre]: blueprint proof of
    lem:identities(bounds): lem:barycentre, applied to the measure
    nu = mu restricted by [y |-> p_(T-t)(x-y)] (Federer 2.4.10) and the
    map X, gives U(t,x)^(-1) W(t,x) in K. Here nu(R^n) = U(t,x), and the
    integral y of X with respect to nu equals W(t,x): for every continuous
    linear functional a, a(y) is the integral of a o X with respect to nu,
    which by the change-of-density formula of Federer 2.4.10 is the
    integral of [z |-> p_(T-t)(x-z) a(X(z))] with respect to mu, that is
    a(W(t,x)) by Federer 2.4.12; the continuous linear functionals
    separate points. *)
Theorem dgpr_identities_barycentre (t : R) (x : X) : t < T -> K ((U (t, x))^-1 *: W (t, x)).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
pose h := real_total_integrand (fun y => p (T - t) (x - y)).
have hU := dgpr_unit_kernel_integral hmu hOmu hMmu x hs.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply: (measure_almost_everywhere_mono hmu _ (measure_almost_everywhere_true hmu)) => y _.
  exists (p (T - t) (x - y))%:E; split; first by apply/real_total_integrand_graph.
  by rewrite lee_fin ltW // dgpr_kernel_gt0.
pose nu := measure_with_density mu h.
have hnu : is_measure nu := measure_with_density_is_measure hmu hpos.
have hmass : nu setT = (U (t, x))%:E.
  rewrite /nu (measure_with_density_laws mu h setT).
  have hWhole : is_measure_subset_integral mu setT h (U (t, x))%:E.
    apply: (measure_integral_graph_equivalent _ hU) => y z.
    exact: iff_sym (partial_zero_extension_whole_graph _ _ y z).
  exact: (measure_upper_integral_unique (measure_upper_integral_specification mu _) hWhole.2.1).
have hXmu := dgpr_standing_X_measurable hS.
have hXnu : is_measure_measurable_function nu
    (partial_function_total (fun y => (Xf y : real_norm_metric_space hNH))).
  constructor.
  - rewrite partial_function_total_domain /measure_almost_everywhere setCT.
    exact: (measure_empty hnu).
  - move=> V hV; apply: (measure_with_density_measurable hmu hpos).
    exact: (measurable_function_open_preimage hXmu hV).
have [k [e he]] := hom_space_finite_basis heX heY.
have hK := dgpr_standing_K_compact hS.
have hKc := dgpr_standing_K_convex hS.
have hXK := dgpr_standing_X_values hS.
have [y [hy hyK]] := dgpr_barycentre_exists he hnu hmass (dgpr_identities_U_pos x ht) hK hKc hXK hXnu.
have [y0 [hy0 _]] := dgpr_barycentre_exists he hmu hMmu ltr01 hK hKc hXK hXmu.
have hW := dgpr_heat_extension_integral hmu hHc hOmu hMmu hHs hXmu
  (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) x hs.
suff -> : W (t, x) = y by [].
apply: (continuous_real_functionals_separate (hN := hNH)) => a ha.
have hya := hy.2 a ha.
have hya' := (@measure_density_integral_iff R X mu nu hmu h _ (measure_with_density_laws mu h) hU.1 hpos
  (hy0.2 a ha).1 (a y)%:E).1 hya.
have hWa := hW.2 a ha.
have e1 : ((a (W (t, x)))%:E : \bar R) = (a y)%:E.
  apply: (measure_integral_unique hWa); apply: (measure_integral_graph_equivalent _ hya') => z c.
  rewrite partial_density_product_graph; split.
  - move=> [a1 [b1 [[v [hv ha1]] [/real_total_integrand_graph hb hc]]]].
    exists (p (T - t) (x - z) *: Xf z); split => //.
    rewrite -hc -ha1 -hb -hv linearZ /= -EFinM; congr EFin; exact: mulrC.
  - move=> [v [hv hc]]; exists (a (Xf z))%:E, (p (T - t) (x - z))%:E.
    split; first by exists (Xf z).
    split; first exact/real_total_integrand_graph.
    rewrite -hc -hv linearZ /= -EFinM; congr EFin; exact: mulrC.
by case: e1.
Qed.

(** Source for [dgpr_identities_B_decomposition]: B = (U/S) U^(-1) W on
    Omega_T; blueprint proof of lem:identities(bounds),(sv). *)
Lemma dgpr_identities_B_decomposition (t : R) (x : X) : t < T ->
  B (t, x) = (U (t, x) / S (t, x)) *: ((U (t, x))^-1 *: W (t, x)).
Proof.
move=> ht; have hU := dgpr_identities_U_pos x ht.
by rewrite /dgpr_heat_B scalerA mulrAC mulfV ?gt_eqF // mul1r.
Qed.

(** Source for [dgpr_identities_bounds]: blueprint lem:identities(bounds)
    and DPGPR 2026, section 3: on Omega_T, rho > 0, U <= S, kappa >= 0,
    U^(-1) W in K, |B| <= Lambda and ||eta|| <= (T - t)^(-1/2). The
    inequality rho <= U is not included; see DgprIdentities.v header. *)
Theorem dgpr_identities_bounds (t : R) (x : X) : t < T ->
  [/\ 0 < rho (t, x) /\ U (t, x) <= S (t, x), 0 <= kappa (t, x),
      K ((U (t, x))^-1 *: W (t, x)), NH (B (t, x)) <= Lam &
      ND (eta (t, x)) <= (Num.sqrt (T - t))^-1].
Proof.
move=> ht; have hU := dgpr_identities_U_pos x ht; have hS0 := dgpr_identities_S_pos x ht.
have hK := dgpr_identities_barycentre x ht.
split; [split; [exact: dgpr_identities_rho_pos | exact: dgpr_identities_U_le_S]
  | exact: dgpr_identities_kappa_ge0 | exact: hK | | exact: dgpr_identities_eta_bound].
have hc0 : 0 <= U (t, x) / S (t, x) by rewrite divr_ge0 // ltW.
have hc1 : U (t, x) / S (t, x) <= 1 by rewrite ler_pdivrMr // mul1r dgpr_identities_U_le_S.
rewrite (dgpr_identities_B_decomposition x ht) /hom_norm (real_seminorm_scale hNH.1) ger0_norm //.
apply: (le_trans (ler_wpM2r (inner_norm_nonnegative BH _) hc1)); rewrite mul1r.
exact: (dgpr_standing_K_norm hS hK).
Qed.

(** Source for [dgpr_identities_sv]: blueprint lem:identities(sv) and
    DPGPR 2026, section 3: if U(t,x) >= (T - t)^(1/2) R(t,x), then
    S(t,x) <= 2 U(t,x), B(t,x) = c U(t,x)^(-1) W(t,x) with
    c = U(t,x)/S(t,x) >= 1/2 and U(t,x)^(-1) W(t,x) in K, hence
    sv_m(B(t,x)) >= lambda/2 by lem:sv(hom). *)
Theorem dgpr_identities_sv (t : R) (x : X) : t < T ->
  Num.sqrt (T - t) * Rr (t, x) <= U (t, x) -> lam / 2 <= dgpr_sv BX hCY heX hm (B (t, x)).
Proof.
move=> ht hUR; have hU := dgpr_identities_U_pos x ht; have hS0 := dgpr_identities_S_pos x ht.
have hK := dgpr_identities_barycentre x ht.
have hc0 : 0 <= U (t, x) / S (t, x) by rewrite divr_ge0 // ltW.
rewrite (dgpr_identities_B_decomposition x ht) dgpr_sv_hom (ger0_norm hc0).
have hc : 2^-1 <= U (t, x) / S (t, x).
  rewrite ler_pdivlMr // /dgpr_heat_S /=.
  move: hUR; set a := U (t, x); set b := Num.sqrt (T - t) * Rr (t, x) => hab; lra.
have hsv := dgpr_standing_K_sv hS hK.
have h2 : 0 <= (2 : R)^-1 by rewrite invr_ge0.
have hl := ltW (dgpr_standing_lambda hS).
have h := ler_pM h2 hl hc hsv.
apply: (le_trans _ h); by rewrite mulrC.
Qed.

End Identities.

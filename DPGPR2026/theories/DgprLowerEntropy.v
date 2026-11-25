(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 4, the
    lower entropy bound (4.2); blueprint dgpr_blueprint.tex,
    lem:lower_entropy.

    Assume (S). Suppose E ⊆ R^n is compact and m rectifiable,
    H^m(E) = h with 0 < h < ∞, and μ_0 = μ ⌞ E. Then there is 0 < s_0
    such that
      H̃(ρ_t) ≥ γ log(γ/h) − γ (log c(n) + 2^(-1) n)
    for T − s_0 < t < T, where c(n) = 1 + 2 (4π)^(n/2) is the constant of
    lem:tube. In particular
      liminf_{t → T−} H̃(ρ_t) ≥ γ log(γ/H^m(E)) − γ (log c(n) + 2^(-1) n).

    The proof follows the blueprint with s = T − t, d = dist(·, E),
    G(x) = exp(−d(x)²/(4s)) and γ_s = ∫ G dL^n. The tangent inequality
    r log r ≥ r log a + r − a, for 0 < a and 0 < r, applied with
    r = ρ_t(x) and a = γ γ_s^(-1) G(x), is the content of Jensen's
    inequality (Federer 2.4.19) used in the blueprint for the probability
    densities γ^(-1) ρ_t and γ_s^(-1) G. The second moment
    ∫ ρ_t d² dL^n ≤ 2 n s γ follows from ρ_t(x) d(x)² ≤ v(x), where
    v(x) = ∫ |x − y|² p_s(x − y) dμ_0 y, since d(x) ≤ |x − y| for y ∈ E and
    μ_0(R^n ∖ E) = 0; the integral ∫ v dL^n = 2 n s γ is computed by
    Fubini's theorem (Federer 2.6.2) and lem:kernel(2), as for
    lem:heat_extension(4) in DgprHeatExtensionMass.v. Then lem:tube
    (DgprTubeEstimate.v) bounds γ_s.

    [dgpr_lower_entropy_of] assumes the Gaussian decay before T of
    ρ log ρ (hypothesis [hG]); [dgpr_lower_entropy] discharges it by
    [dgpr_entropy_gaussian] (DgprEntropy.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormMetricSubtractContinuity InnerProductUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner
  ScalarInnerProduct InnerMetric PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialExtendedOrderLoci
  PartialProductSections MeasureUP MeasureSplit InnerNormInequalities CircularTrigonometrySealed MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasureIntegralBounds MeasureNonnegativeIntegral MeasureRestriction SummableRealFunctionUP
  SummableRealArithmetic CompleteMetricUP NormClassOneUP NormClassZeroTopology NormClassZeroScalarProduct
  NormClassZeroFiniteSum NormOpenDomainLaws NormDifferentialUP ScalarNormMetricCompleteness LocalUniquenessExample
  TotalScalarLpUP TotalScalarArithmetic ScalarCountableEmbedding ProductMeasure ProductBorelRectangles
  ProductFunctionMeasurability ProductFunctionFubini ParameterizedIntegralUP ParameterizedIntegral
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct CountablyMeasurableFunctions
  CountablyMeasurableNullModification EuclideanNormCountableBase EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceSealed
  HausdorffMeasure RectifiableSetUP RadonMeasureUP SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprParameterIntegralDifferential DgprHeatKernel DgprHeatKernelFamily
  DgprHeatExtension DgprHeatSemiconvex DgprHeatExtensionMass DgprLebesgueIntegrals DgprTubeEstimate
  DgprGrowthClasses DgprStanding DgprHeatObjects DgprIdentities DgprLemma31Main DgprEntropy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EntropyTangent.
Variable R : realType.
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_entropy_tangent_lower]: r log r ≥ r log a + r − a
    for 0 < a and 0 < r, from log(a/r) ≤ a/r − 1 (Federer 2.4.12-13);
    this is the tangent form of Jensen's inequality (Federer 2.4.19) for
    [r ↦ r log r] in the proof of lem:lower_entropy. *)
Lemma dgpr_entropy_tangent_lower (a r : R) : 0 < a -> 0 < r -> r * LOG a + r - a <= r * LOG r.
Proof.
move=> ha hr.
have ht := real_logarithm_tangent (divr_gt0 ha hr).
rewrite real_logarithm_ratio // in ht.
have h : r * (LOG a - LOG r) <= r * (a / r - 1) by rewrite ler_pM2l.
have e1 : r * (a / r - 1) = a - r by field; rewrite gt_eqF.
rewrite e1 mulrBr in h.
move: h; set p := r * LOG a; set q := r * LOG r; lra.
Qed.
End EntropyTangent.

Section KernelMass.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation S := (real_norm_metric_space hA).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Hypothesis hOpen : forall A : set X, @open T A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Local Notation mu := (product_measure hLL hnu).
Local Notation hmu := (product_measure_is_measure hLL hnu).
Variable k : X -> R.
Hypothesis hk : norm_class_zero N A1 setT k.
Variable Kb : R.
Hypothesis hKb : forall z, `|k z| <= Kb.
Hypothesis hk0 : forall z, 0 <= k z.
Variable c : R.
Hypothesis hkc : is_measure_integral LL (real_total_integrand k) c%:E.
Local Notation v := (dgpr_convolution hnu hZ1 (fun _ : X => 1 : R^o) k).

(** Source for [dgpr_kernel_general_difference_measurable]: the
    continuous map [(x,y) ↦ k(x − y)] is L^n × ν measurable (Federer
    2.3.2, 2.6.2), as in DgprHeatExtensionMass.v for k = p_s; proof of
    lem:lower_entropy. *)
Lemma dgpr_kernel_general_difference_measurable :
  is_measure_measurable_function mu
    (partial_function_total (fun q : T * T => (k (q.1 - q.2) : S))).
Proof.
have hk' : continuous (fun z : T => (k z : S)).
  move=> z; exact: (@norm_class_zero_continuous_at R X R^o N A1 hN hA setT k z hk I).
have hsub := @real_norm_metric_subtract_continuous R X N hN.
have hK : continuous (fun q : T * T => (k (q.1 - q.2) : S)).
  by move=> q; apply: (continuous_comp (hsub q)); exact: hk'.
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hmu.
- move=> W hW; rewrite partial_function_total_preimage; apply: (dgpr_product_open_measurable hnu hOpen).
  by apply: open_comp hW => q _; exact: hK.
Qed.

(** Source for [dgpr_kernel_convolution_mass]: for a nonnegative bounded
    continuous kernel k with ∫ k dL^n = c, the function
    v(x) = ∫ k(x − y) dν y satisfies ∫ v dL^n = c ν(R^n), by Fubini's
    theorem (Federer 2.6.2) and the invariance of L^n under translations
    (2.7.16); proof of lem:lower_entropy, with k(z) = |z|² p_s(z). *)
Theorem dgpr_kernel_convolution_mass : is_measure_integral LL (real_total_integrand v) (c * m)%:E.
Proof.
pose F := real_total_integrand (fun q : X * X => k (q.1 - q.2)).
have hF : is_measure_measurable_function mu F.
  exact: (scalar_real_integrand_measurable hmu dgpr_kernel_general_difference_measurable).
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus F).
  apply: (measure_almost_everywhere_mono hmu _ (measure_almost_everywhere_true hmu)) => q _.
  exists (k (q.1 - q.2))%:E; split; first by rewrite real_total_integrand_graph.
  by rewrite lee_fin hk0.
have [hI _] := nonnegative_measurable_function_integral hmu hF hpos.
have hfin : (nu setT < +oo)%E by rewrite hmass ltry.
have hWhole := @product_whole_countably_measurable R X X LL nu hLL hnu
  (euclidean_lebesgue_countably_measurable R n)
  (finite_measurable_set_countably_measurable (measure_measurable_whole hnu) hfin).
have hCount := countably_measurable_function_on_countable_source hmu
  (@CountablyMeasurableNullModification.extended_real_zero_closed R) hWhole hI.1.
have [hV hH] := @product_function_fubini R X X LL nu hLL hnu F _ hI hCount.
have hb : is_measure_integral nu (real_total_integrand (fun _ : X => c)) (c * m)%:E.
  exact: (dgpr_constant_integral hnu hmass c).
have hgb : is_measure_integral nu (real_total_integrand (fun _ : X => c)) (measure_lower_integral mu F).
  apply: (measure_integral_graph_equivalent _ hH) => y a.
  rewrite parameterized_integral_specification real_total_integrand_graph.
  have hy : is_measure_integral LL (partial_product_horizontal_section F y) c%:E.
    have h := dgpr_translation_integral (- y) hkc.
    apply: (measure_integral_graph_equivalent _ h) => x z.
    change (partial_function_graph (real_total_integrand (fun x => k (x + - y))) x z <->
      partial_function_graph F (x, y) z).
    by rewrite !real_total_integrand_graph.
  split; first by move=> ha; exact: esym (measure_integral_unique ha hy).
  by move=> <-.
have hVb := measure_integral_unique hgb hb.
rewrite -hVb.
apply: (measure_integral_graph_equivalent _ hV) => x a.
rewrite parameterized_integral_specification real_total_integrand_graph.
have hx : is_measure_integral nu (partial_product_vertical_section F x) (v x)%:E.
  apply: (measure_integral_graph_equivalent _ (dgpr_one_integral hnu hOpen hmass x hk hKb)) => y z.
  change (partial_function_graph (real_total_integrand (fun y => k (x - y))) y z <->
    partial_function_graph F (x, y) z).
  by rewrite !real_total_integrand_graph.
split; first by move=> ha; exact: esym (measure_integral_unique ha hx).
by move=> <-.
Qed.
End KernelMass.

Section SecondMomentKernel.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).

(** Source for [dgpr_moment_kernel]: the kernel [z ↦ |z|² p_s(z)] of
    lem:kernel(2); proof of lem:lower_entropy. *)
Definition dgpr_moment_kernel (s : R) (z : X) : R := N z ^+ 2 * p s z.

(** Source for [dgpr_moment_kernel_class_zero]: the kernel
    [z ↦ |z|² p_s(z)] is continuous for 0 < s, since
    |z|² = Σ_i z_i z_i (Federer 1.7.1); proof of lem:lower_entropy. *)
Lemma dgpr_moment_kernel_class_zero (s : R) : 0 < s ->
  norm_class_zero N A1 setT (dgpr_moment_kernel s).
Proof.
move=> hs.
have hF : norm_class_zero N A1 setT (fun z : X => \sum_(i < n) z i * (z i * p s z)).
  apply: (norm_class_zero_finite_sum hN hA (fun x _ => norm_full_domain_interior N x)) => i.
  apply: (norm_class_zero_scalar_product hA (dgpr_coordinate_class_zero i)).
  exact: (norm_class_zero_scalar_product hA (dgpr_coordinate_class_zero i) (dgpr_kernel_class_zero hs)).
have e : (fun z : X => \sum_(i < n) z i * (z i * p s z)) = dgpr_moment_kernel s.
  apply: funext => z; rewrite /dgpr_moment_kernel (inner_norm_sqr (@euclidean_inner_productP R n)).
  rewrite /euclidean_inner_product mulr_suml; apply: eq_bigr => i _; exact: mulrA.
by rewrite -e.
Qed.

(** Source for [dgpr_moment_kernel_bound]: 0 ≤ |z|² p_s(z) ≤
    4 s (4πs)^(-n/2); lem:kernel(4) (DgprHeatExtension.v). *)
Lemma dgpr_moment_kernel_bound (s : R) (z : X) : 0 < s ->
  0 <= dgpr_moment_kernel s z /\ `|dgpr_moment_kernel s z| <= 4 * s * dgpr_kernel_constant n s.
Proof.
move=> hs; have h0 : 0 <= dgpr_moment_kernel s z.
  by rewrite /dgpr_moment_kernel mulr_ge0 ?sqr_ge0 // ltW // dgpr_kernel_gt0.
by split => //; rewrite ger0_norm //; exact: dgpr_kernel_sqr_weight.
Qed.
End SecondMomentKernel.

Section LowerEntropy.
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
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation RnM := (inner_metric_space BX).
Local Notation HH := (@hausdorff_measure R RnM m).
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
Local Notation hZ1 := (@scalar_norm_metric_complete R).
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
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation exp := (@RealExponential.exponential R).

(** Source for [dgpr_tube_constant]: the constant c(n) = 1 + 2 (4π)^(n/2)
    of lem:tube. *)
Definition dgpr_tube_constant : R := 1 + 2 * Num.sqrt (4 * dgpr_pi R) ^+ n.

(** Source for [dgpr_tube_constant_gt0]: 0 < c(n); lem:tube. *)
Lemma dgpr_tube_constant_gt0 : 0 < dgpr_tube_constant.
Proof. by rewrite /dgpr_tube_constant ltr_pwDl // mulr_ge0 // exprn_ge0 // sqrtr_ge0. Qed.

Variable Ec : set RnM.
Hypothesis hEc : mu0 = measure_restrict mu Ec.

(** Source for [dgpr_lower_entropy_null]: μ_0(R^n ∖ E) = 0 for
    μ_0 = μ ⌞ E (Federer 2.1.2); proof of lem:lower_entropy. *)
Lemma dgpr_lower_entropy_null : measure_almost_everywhere mu0 Ec.
Proof.
rewrite /measure_almost_everywhere hEc /measure_restrict setICr.
exact: measure_empty (dgpr_standing_mu_measure hS).
Qed.

Section Distance.
Variable dE : RnM -> R.
Hypothesis hdE : is_metric_set_distance Ec dE.

(** Source for [dgpr_lower_entropy_moment_pointwise]: blueprint proof of
    lem:lower_entropy: ρ_t(x) d(x)² ≤ v(x) = ∫ |x − y|² p_s(x − y) dμ_0 y
    for t < T and s = T − t, since d(x) ≤ |x − y| for y ∈ E and
    μ_0(R^n ∖ E) = 0. *)
Lemma dgpr_lower_entropy_moment_pointwise (t : R) (x : X) : t < T ->
  rho (t, x) * dE x ^+ 2 <=
    dgpr_convolution hmu0 hZ1 (fun _ : X => 1 : R^o) (dgpr_moment_kernel (T - t)) x.
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have h1 := dgpr_one_integral hmu0 hOmu0 hMmu0 x (dgpr_kernel_class_zero hs)
  (fun z => dgpr_kernel_abs_le z hs).
have h1s := real_total_integral_scale hmu0 (dE x ^+ 2) h1.
have h2 := dgpr_one_integral hmu0 hOmu0 hMmu0 x (dgpr_moment_kernel_class_zero hs)
  (fun z => (dgpr_moment_kernel_bound z hs).2).
rewrite mulrC; rewrite -lee_fin.
apply: (measure_integral_monotone hmu0 h1s h2).
apply: (measure_almost_everywhere_mono hmu0 _ dgpr_lower_entropy_null) => y hy.
exists (dE x ^+ 2 * p (T - t) (x - y))%:E, (dgpr_moment_kernel (T - t) (x - y))%:E.
split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin /dgpr_moment_kernel; apply: ler_wpM2r; first exact: ltW (dgpr_kernel_gt0 _ hs).
have hd0 := metric_set_distance_nonnegative hdE x.
have hdl := metric_set_distance_lower hdE x hy.
rewrite inner_metric_distanceE in hdl.
by rewrite ler_sqr // nnegrE // inner_norm_nonnegative.
Qed.

(** Source for [dgpr_lower_entropy_moment]: blueprint proof of
    lem:lower_entropy: ∫ v dL^n = 2 n s γ for v as in
    [dgpr_lower_entropy_moment_pointwise], by Fubini's theorem (Federer
    2.6.2) and lem:kernel(2). *)
Lemma dgpr_lower_entropy_moment (s : R) : 0 < s ->
  is_measure_integral LL
    (real_total_integrand (dgpr_convolution hmu0 hZ1 (fun _ : X => 1 : R^o) (dgpr_moment_kernel s)))
    (2 * n%:R * s * gamma)%:E.
Proof.
move=> hs.
have hc : is_measure_integral LL (real_total_integrand (dgpr_moment_kernel s)) (2 * n%:R * s)%:E.
  have h := @dgpr_kernel_moment R n s hs; exact: h.
exact: (@dgpr_kernel_convolution_mass R n mu0 hmu0 hOmu0 gamma hMmu0 (dgpr_moment_kernel s)
  (dgpr_moment_kernel_class_zero hs) _ (fun z => (dgpr_moment_kernel_bound z hs).2)
  (fun z => (dgpr_moment_kernel_bound z hs).1) _ hc).
Qed.

(** Source for [dgpr_lower_entropy_gaussian_positive]: blueprint proof of
    lem:lower_entropy: γ_s = ∫ exp(−d(x)²/(4s)) dL^n x > 0 for 0 < s and
    E nonempty, since p_s(x − y) ≤ (4πs)^(-n/2) exp(−d(x)²/(4s)) for
    y ∈ E and ∫ p_s(x − y) dL^n x = 1 (lem:kernel(1), Federer 2.7.16). *)
Lemma dgpr_lower_entropy_gaussian_positive (s g : R) (y : X) : 0 < s -> Ec y ->
  is_measure_integral LL (real_total_integrand (fun x : X => exp (- dE x ^+ 2 / (4 * s)))) g%:E ->
  0 < g.
Proof.
move=> hs hy hg.
have h1 := dgpr_translation_integral (- y) (dgpr_kernel_mass n hs).
have h2 := real_total_integral_scale hLL (dgpr_kernel_constant n s) hg.
have hc : 0 < dgpr_kernel_constant n s.
  rewrite /dgpr_kernel_constant invr_gt0 exprn_gt0 // sqrtr_gt0.
  by rewrite mulr_gt0 // mulr_gt0 // (@dgpr_pi_gt0 R).
have hle : 1 <= dgpr_kernel_constant n s * g.
  apply: (dgpr_integral_le hLL _ h1 h2) => x.
  rewrite /dgpr_heat_kernel -/(dgpr_kernel_constant n s); apply: ler_wpM2l; first exact: ltW.
  apply: dgpr_exponential_le; rewrite !mulNr lerN2; apply: ler_wpM2r.
    by rewrite invr_ge0 ltW // mulr_gt0.
  have hd0 := metric_set_distance_nonnegative hdE x.
  have hdl := metric_set_distance_lower hdE x hy.
  rewrite inner_metric_distanceE in hdl.
  by rewrite ler_sqr // nnegrE // inner_norm_nonnegative.
have : 0 < dgpr_kernel_constant n s * g by apply: lt_le_trans hle.
by rewrite pmulr_rgt0.
Qed.

Section LowerEntropyConditional.
Hypothesis hG : dgpr_gaussian_decay_before hA T (fun q : TX => rho q * LOG (rho q)).

(** Source for [dgpr_lower_entropy_fixed]: blueprint proof of
    lem:lower_entropy, at a fixed time t < T with s = T − t:
    H(ρ_t) ≥ γ log(γ/γ_s) − 2^(-1) n γ. With a = γ/γ_s, the tangent
    inequality gives ρ_t log ρ_t ≥ ρ_t log a − (4s)^(-1) ρ_t d² + ρ_t −
    a G ≥ ρ_t log a − (4s)^(-1) v + ρ_t − a G, whose integral is
    γ log a − 2^(-1) n γ + γ − γ. *)
Lemma dgpr_lower_entropy_fixed (t g : R) : t < T ->
  is_measure_integral LL (real_total_integrand (fun x : X => exp (- dE x ^+ 2 / (4 * (T - t))))) g%:E ->
  0 < g ->
  gamma * LOG (gamma / g) - 2^-1 * n%:R * gamma <= dgpr_entropy hS t.
Proof.
move=> ht hgI hg0.
have hs : 0 < T - t by rewrite subr_gt0.
have hgam := dgpr_standing_gamma hS.
have [hH _ _] := dgpr_entropy_derivative_of hG.
have [_ _ _ hmass] := dgpr_identities_mass hS ht.
have hv := dgpr_lower_entropy_moment hs.
have ha : 0 < gamma / g by rewrite divr_gt0.
have h1 := real_total_integral_scale hLL (LOG (gamma / g)) hmass.
have h2 := real_total_integral_scale hLL (- (4 * (T - t))^-1) hv.
have h3 := real_total_integral_add hLL h1 h2.
have h4 := real_total_integral_add hLL h3 hmass.
have h5 := real_total_integral_scale hLL (gamma / g) hgI.
have h6 := real_total_integral_subtract hLL h4 h5.
have hb := dgpr_integral_le hLL _ h6 (hH t ht).
apply: le_trans (hb _); last first.
  move=> x /=.
  have hr := dgpr_identities_rho_pos hS x ht.
  have hG0 : 0 < exp (- dE x ^+ 2 / (4 * (T - t))) := real_exponential_positive (@RealExponential.laws R) _.
  have hmp := dgpr_lower_entropy_moment_pointwise x ht.
  have htan := dgpr_entropy_tangent_lower (mulr_gt0 ha hG0) hr.
  rewrite real_logarithm_product // (real_logarithm_exponential (@RealExponential.laws R)) in htan.
  move: htan hmp.
  set r := rho (t, x); set L := LOG (gamma / g); set D := dE x ^+ 2; set G := exp _.
  set V := dgpr_convolution _ _ _ _ x; set w := (4 * (T - t))^-1.
  have hw : 0 < w by rewrite invr_gt0 mulr_gt0.
  have e1 : r * (L + - D / (4 * (T - t))) = L * r - (r * D) * w by rewrite /w; ring.
  rewrite e1 => htan hmp.
  have hmw : (r * D) * w <= V * w by rewrite ler_pM2r.
  have e2 : - (4 * (T - t))^-1 * V = - (V * w) by rewrite /w; ring.
  rewrite e2; lra.
have e : LOG (gamma / g) * gamma + - (4 * (T - t))^-1 * (2 * n%:R * (T - t) * gamma) + gamma -
    gamma / g * g = gamma * LOG (gamma / g) - 2^-1 * n%:R * gamma.
  by field; rewrite !gt_eqF.
by rewrite e.
Qed.

End LowerEntropyConditional.
End Distance.
Section LowerEntropyMain.
Hypothesis hG : dgpr_gaussian_decay_before hA T (fun q : TX => rho q * LOG (rho q)).

(** Source for [dgpr_lower_entropy_of]: DPGPR 2026, (4.2), and blueprint
    lem:lower_entropy, under the hypothesis [hG]: if E is compact and
    m rectifiable, H^m(E) = h with 0 < h, and μ_0 = μ ⌞ E, then there is
    0 < s_0 with H̃(ρ_t) ≥ γ log(γ/h) − γ (log c(n) + 2^(-1) n) for
    T − s_0 < t < T. The number s_0 is that of lem:tube. *)
Theorem dgpr_lower_entropy_of (h : R) :
  compact Ec -> is_m_rectifiable m Ec -> HH Ec = h%:E -> 0 < h ->
  exists s0 : R, 0 < s0 /\ forall t : R, T - s0 < t -> t < T ->
    gamma * LOG (gamma / h) - gamma * (LOG dgpr_tube_constant + 2^-1 * n%:R) <= dgpr_entropy_tilde hS t.
Proof.
move=> hc hr hh hh0.
have /andP [hm0 hmn] := hm.
have hgam := dgpr_standing_gamma hS.
have hne : Ec !=set0.
  apply/set0P; apply/negP => /eqP e0.
  have := measure_empty (hausdorff_measure_is_measure RnM m).
  by rewrite -e0 hh => /eqP; rewrite eqe gt_eqF.
pose dE := MetricSetDistance.value hne.
have hdE : is_metric_set_distance Ec dE := MetricSetDistance.laws hne.
have [y hy] := hne.
have hpos : (0 < HH Ec)%E by rewrite hh lte_fin.
have [s0 [/andP [hs0 hs01] htube]] := dgpr_tube_estimate hm0 hmn hc hr hpos hdE.
exists s0; split => // t h1 h2.
have hs : 0 < T - t by rewrite subr_gt0.
have hss0 : T - t < s0 by rewrite ltrBlDr addrC -ltrBlDr.
have [g hgI] := dgpr_tube_summable hc hdE hs.
have hg0 := dgpr_lower_entropy_gaussian_positive hdE hs hy hgI.
have hfix := dgpr_lower_entropy_fixed hdE hG h2 hgI hg0.
have hgt := htube (T - t) (introT andP (conj hs hss0)) g hgI.
rewrite hh -EFinM lee_fin -/dgpr_tube_constant in hgt.
have hc0 := dgpr_tube_constant_gt0.
have hq : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0.
have hqk : 0 < Num.sqrt (T - t) ^+ (n - m) by rewrite exprn_gt0.
have hlog : LOG g <= LOG dgpr_tube_constant + 2^-1 * (n - m)%:R * LOG (T - t) + LOG h.
  have hp : 0 < dgpr_tube_constant * Num.sqrt (T - t) ^+ (n - m) * h by rewrite !mulr_gt0.
  rewrite -(real_logarithm_order hg0 hp) in hgt.
  apply: le_trans hgt _.
  rewrite !real_logarithm_product ?mulr_gt0 // dgpr_logarithm_natural_power //.
  rewrite dgpr_logarithm_sqrt //.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
rewrite real_logarithm_ratio // in hfix.
rewrite /dgpr_entropy_tilde real_logarithm_ratio //.
have hgl := ler_wpM2l (ltW hgam) hlog.
move: hfix hgl; set H := dgpr_entropy hS t; set Lg := LOG g; set Lc := LOG dgpr_tube_constant.
set Ls := LOG (T - t); set Lh := LOG h; set La := LOG gamma; set k := (n - m)%:R.
move=> hfix hgl.
have e1 : gamma * (Lc + 2^-1 * k * Ls + Lh) = gamma * Lc + 2^-1 * k * gamma * Ls + gamma * Lh by ring.
have e2 : gamma * (La - Lh) - gamma * (Lc + 2^-1 * n%:R) =
  gamma * La - gamma * Lh - gamma * Lc - 2^-1 * n%:R * gamma by ring.
have e3 : gamma * (La - Lg) = gamma * La - gamma * Lg by ring.
rewrite e1 in hgl; rewrite e3 in hfix; rewrite e2.
lra.
Qed.
End LowerEntropyMain.

(** Source for [dgpr_lower_entropy]: DPGPR 2026, (4.2), and blueprint
    lem:lower_entropy: if E is compact and m rectifiable, H^m(E) = h
    with 0 < h, and μ_0 = μ ⌞ E, then there is 0 < s_0 with
    H̃(ρ_t) ≥ γ log(γ/h) − γ (log c(n) + 2^(-1) n) for T − s_0 < t < T;
    in particular the lower limit of H̃(ρ_t) as t → T− is at least the
    right side. *)
Theorem dgpr_lower_entropy (h : R) :
  compact Ec -> is_m_rectifiable m Ec -> HH Ec = h%:E -> 0 < h ->
  exists s0 : R, 0 < s0 /\ forall t : R, T - s0 < t -> t < T ->
    gamma * LOG (gamma / h) - gamma * (LOG dgpr_tube_constant + 2^-1 * n%:R) <= dgpr_entropy_tilde hS t.
Proof. exact: (dgpr_lower_entropy_of (dgpr_entropy_gaussian hS)). Qed.

End LowerEntropy.

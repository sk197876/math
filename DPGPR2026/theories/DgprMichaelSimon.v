(** De Philippis, Gennaioli, Pigati and Rindler (2026), Theorem 1.6;
    blueprint thm:MS: the reduction of the anisotropic Michael–Simon
    inequality to thm:main.

    The standing data of the section MichaelSimon are the following. The
    integrand F is of class 1 relative to G(n, k) with positive values
    ([dgpr_integrand]) and satisfies (AC1) ([dgpr_AC1]). The varifold
    V ∈ RV_k(R^n) satisfies ‖V‖(R^n) < ∞ and Θ^k(‖V‖, x) ≥ 1 for ‖V‖
    almost all x. The linear functional S on D(R^n, R^n) satisfies
    S(g) = δ_F V(g) for every g ∈ D(R^n, R^n), in the sense of
    [is_dgpr_first_variation]. The Radon measure ν over R^n satisfies
    ν(R^n) < ∞ and represents the variation ‖S‖ of Federer 4.1.5 on the
    nonnegative continuous functions with compact support, as in
    mr:functionals. Thus δ_F V enters as a hypothesis S with its
    characterising property, and the hypothesis that δ_F V is
    representable by integration with ‖δ_F V‖(R^n) < ∞ is the existence
    of ν (docs/divergences.md).

    Theorem [dgpr_MS_reduction] contains the part of the proof of thm:MS
    that does not use thm:main. Let λ = λ(F) and Λ = Λ(F) (def:BF,
    lem:KF). There are a Borel set M' ⊆ M, a density θ and a map X such
    that ‖V‖ = (H^k ⌞ M') ⌞ θ and the data Y = R^n, K = K_F, λ, Λ, M',
    θ, X, Υ = −S and ‖Υ‖ = ν satisfy mr:hypotheses_main
    ([dgpr_main_hypotheses]). Here X(x) = B_F(t(x)), where t is a Borel
    map of R^n into G(n, k) with t(x) = Tan^k(‖V‖, x) for ‖V‖ almost all
    x and V = [x ↦ (x, t(x))]_# ‖V‖ ([allard_3_5_1_b_pushforward]). The
    relation Υ(g) = −σ(Dg) follows from lem:first_variation and this
    representation of V ([dgpr_MS_transfer], [dgpr_MS_constraint]).

    Theorem [dgpr_theorem_1_6_from_main] deduces (eq:MS:MS),
        ‖V‖(R^n) ≤ C H^k(M)^{1/k} ‖δ_F V‖(R^n),
    and, if k > 1, (eq:MS:sobolev),
        ‖V‖(R^n)^{(k − 1)/k} ≤ C ‖δ_F V‖(R^n),
    from the conclusion of thm:main for λ(F), Λ(F) and a constant
    0 ≤ C ([dgpr_main_inequality]); here M = [dgpr_MS_set k ‖V‖]
    (DgprVarifoldWeight.v). Theorem 1.6 itself is not stated in this
    file; it follows once thm:main is proved. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  cardinality reals topology constructive_ereal ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities InnerMetric
  LinearBasis Hom HomInner GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  HilbertFormCompactness RealNormUP NormMetric RealMetricBackground FiniteNormEquivalence
  NormBoundedBilinearUP BoundedBilinearContinuity Bilinear NormDifferentialUP NormClassOneUP
  NormRegularity RelativeClassUP ConvexHull InnerConvex PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasureBasic MeasureRestriction MeasureDensity
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureStepIntegralIdentification PushforwardIntegral SummableRealFunctionUP RadonMeasureUP
  RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel BorelFunctionUP BorelFunctionBasic
  FunctionLatticeUP CompactSupportFunctionUP DistributionVariationUP SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation HausdorffMeasure RectifiableSetUP RealPower ExtendedSupremumUP
  BVCurveMeasurable MeasurePushforward RealPowerSuccessor MeasureAlmostUP MeasureAlmostBasic MetricDensities.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds AllardRectifiableVarifolds AllardTangentMeasurability AllardRectifiableStructure
  AllardImageVarifoldMaps AllardSetVarifold.
From DPDRG Require Import DdgAnisotropicIntegrand.
From DPGPR Require Import DgprSingularValue DgprMainHypotheses DgprAnisotropicIntegrand DgprKF
  DgprVarifoldWeight DgprFirstVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section VariationOpposite.
Variable R : realType.
Variable X : choiceType.
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable E : lmodType R.
Variable value : Hom E (GRing.Lmodule.clone R (X -> Y) _).
Variable S : Hom E R^o.

(** Source for [dgpr_variation_values_opp]: Federer 4.1.5, p. 349: the
    set of numbers S(φ) with |φ(x)| ≤ f(x) for every x, whose supremum is
    ‖S‖(f), is the same for S and −S, because [φ ↦ −φ] is linear and
    |−φ(x)| = |φ(x)|. Supporting lemma. *)
Lemma dgpr_variation_values_opp (f : X -> R) :
  distribution_variation_values (inner_norm hCY) value (- S) f =
  distribution_variation_values (inner_norm hCY) value S f.
Proof.
have hv (phi : E) x : value (- phi) x = - value phi x.
  have e : value (- phi) = - value phi := raddfN (hom_as_linear value) phi.
  by rewrite e.
have hs (phi : E) : S (- phi) = - S phi := raddfN (hom_as_linear S) phi.
apply/seteqP; split=> a [phi [hphi <-]].
- exists (- phi); split.
  + by move=> x; rewrite hv inner_normN.
  + exact: (hs phi).
- exists (- phi); split.
  + by move=> x; rewrite hv inner_normN.
  + have e : (- S) (- phi) = - S (- phi) by [].
    by rewrite e (hs phi) opprK.
Qed.

(** Source for [dgpr_variation_value_opp]: blueprint thm:MS,
    “‖Υ‖ = ‖δ_F V‖” for Υ = −δ_F V: ‖−S‖(f) = ‖S‖(f) (Federer 4.1.5,
    p. 349). Supporting lemma. *)
Lemma dgpr_variation_value_opp (f : X -> R) c :
  is_distribution_variation_value (inner_norm hCY) value (- S) f c <->
  is_distribution_variation_value (inner_norm hCY) value S f c.
Proof. by rewrite /is_distribution_variation_value dgpr_variation_values_opp. Qed.

End VariationOpposite.

(** Source for [dgpr_real_norm_line_continuous]: the absolute value
    norm and the real line induce the same topology on R; continuity
    into one is continuity into the other. Supporting lemma. *)
Lemma dgpr_real_norm_line_continuous (R : realType) (T : topologicalType) (f : T -> R) :
  continuous (fun p : T => (f p : real_norm_metric_space (@scalar_absolute_value_norm R))) ->
  continuous (fun p : T => (f p : real_line_metric R)).
Proof.
move=> hf p W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f p : real_line_metric R) W) hW.
have hW' : nbhs (f p : real_norm_metric_space (@scalar_absolute_value_norm R)) W.
  apply/(metricType_numDomainType.nbhs_mdistP (f p : real_norm_metric_space (@scalar_absolute_value_norm R)) W).
  by exists e=> // y hy; apply: hball.
exact: hf p W hW'.
Qed.

(** Source for [dgpr_inner_real_norm_continuous]: an inner product
    space carries the same topology as a metric space and as a normed
    space; continuity into the former is continuity into the latter.
    Supporting lemma. *)
Lemma dgpr_inner_real_norm_continuous (R : realType) (T : topologicalType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : T -> V) :
  continuous (fun p : T => (f p : inner_metric_space hB)) ->
  continuous (fun p : T => (f p : real_norm_metric_space (inner_norm_real_norm hB))).
Proof.
move=> hf p W hW.
have hW' : nbhs (f p : inner_metric_space hB) W := (inner_real_norm_same_nbhs hB (f p) W).2 hW.
exact: hf p W hW'.
Qed.

Section MichaelSimon.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation RnM := (inner_metric_space hBn).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hH).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).

Variable F : Hom Rn Rn -> R.
Hypothesis hF : dgpr_integrand k F.
Hypothesis hAC : dgpr_AC1 k F.
Variable E : lmodType R.
Variable ev : E -> Rn -> Rn.
Hypothesis hE : is_smooth_function_space hNn hNn setT ev.
Variable V : set GB -> \bar R.
Hypothesis hV : is_rectifiable_varifold V.
Hypothesis hVf : (V setT < +oo)%E.
Local Notation W := (varifold_weight V).
Hypothesis hdens : measure_almost_everywhere W
  [set x | exists t : \bar R, partial_function_graph (@metric_density R RnM k W) x t /\ (1 <= t)%E].
Variable S : Hom (smooth_test_space hE) R^o.
Hypothesis hS : forall (g : smooth_test_space hE) (Dg : Rn -> Hom Rn Rn),
  (forall x, has_norm_differential Nn Nn setT (smooth_test_value hE g) x (Dg x)) ->
  is_dgpr_first_variation V F (smooth_test_value hE g) Dg (S g).
Variable nu : set (real_norm_metric_space hNn) -> \bar R.
Hypothesis hnu : is_measure nu.
Hypothesis hnur : is_radon_measure nu.
Hypothesis hnug : forall f,
  positive_function_lattice (@compactly_supported_continuous_functions R (real_norm_metric_space hNn)) f ->
  exists b : R, is_distribution_variation_value Nn (smooth_test_values_hom hE) S f b%:E /\
    is_measure_integral nu (real_total_integrand f) b%:E.
Hypothesis hnuf : (nu setT < +oo)%E.

(** Source for [dgpr_MS_test_integrand_borel]: blueprint thm:MS: if g
    is of class 1 with differential Dg, then [(x, S) ↦ B_F(S) • Dg(x)] is
    continuous on G_k(R^n) (def:BF, [dgpr_B_continuous]), hence a Borel
    function. Supporting lemma. *)
Lemma dgpr_MS_test_integrand_borel (g : Rn -> Rn) (Dg : Rn -> Hom Rn Rn) :
  is_norm_class_one_field Nn Nn setT g Dg ->
  is_borel_function ((fun z : GB => HI (dgpr_B k F (set_val z.2 : Hom Rn Rn)) (Dg z.1))
    : GB -> real_line_metric R).
Proof.
move=> hg.
have hb : norm_bounded_bilinear NH NH N1 HI.
  split; first exact: (inner_bilinear hH).
  exists 1; split=> // u v; rewrite mul1r; exact: (inner_cauchy hH u v).
have h1 : continuous (fun z : GB => (dgpr_B k F (set_val z.2 : Hom Rn Rn) : real_norm_metric_space hNH)).
  exact: (continuous_function_composition (@grassmann_bundle_plane_continuous R n k)
    (dgpr_B_continuous hF.1)).
have h2 : continuous (fun z : GB => (Dg z.1 : real_norm_metric_space hNH)).
  apply: dgpr_inner_real_norm_continuous.
  exact: (continuous_function_composition (@grassmann_bundle_point_continuous R n k)
    (class_one_differential_continuous hg)).
have h3 := @bounded_bilinear_continuous_factors R _ _ R^o NH NH N1 hNH hNH hN1 HI hb GB _ _ h1 h2.
exact: (continuous_borel_function (dgpr_real_norm_line_continuous h3)).
Qed.

(** Source for [dgpr_MS_transfer]: blueprint thm:MS, (eq:MS:V), with
    Federer 2.4.18(1), p. 90: if t is a Borel map of R^n into G(n, k),
    V = [x ↦ (x, t(x))]_# ‖V‖ and h is a Borel function on G_k(R^n), then
    ∫ h dV = ∫ h(x, t(x)) d‖V‖ x whenever the left side exists.
    Supporting lemma. *)
Lemma dgpr_MS_transfer (t : RnM -> GA) (h : GB -> R) (a : \bar R) :
  is_borel_function t ->
  V = measure_pushforward (fun x : RnM => ((x, t x) : GB)) W ->
  is_borel_function (h : GB -> real_line_metric R) ->
  is_measure_integral V (real_total_integrand h) a ->
  is_measure_integral W (real_total_integrand (fun x : RnM => h ((x, t x) : GB))) a.
Proof.
move=> ht hVt hh hI.
have [hm _ hbr _] := dgpr_weight_laws hV hVf.
pose u := fun x : RnM => ((x, t x) : GB).
have hc : is_borel_function ((h \o u) : RnM -> real_line_metric R).
  exact: (borel_function_composition (graph_map_borel ht) hh).
have hm1 := borel_map_measure_measurable hm hbr hc.
have hm2 := measurable_partial_real_embedding hm hm1.
have he x y : partial_function_graph (real_total_integrand (h \o u)) x y <->
    partial_function_graph (partial_function_precompose u (real_total_integrand h)) x y.
  exact: (iff_trans (real_total_integrand_graph (h \o u) x y)
    (iff_sym (real_total_integrand_graph h (u x) y))).
have hm3 := measurable_function_graph_equivalent he hm2.
rewrite hVt in hI.
have hI' := (measure_pushforward_integral_iff hm hm3 a).2 hI.
exact: (measure_integral_graph_equivalent (fun x y => iff_sym (he x y)) hI').
Qed.

(** Source for [dgpr_MS_constraint]: blueprint thm:MS:
    Υ(g) = −∫ B_F(S) • Dg(x) dV(x, S) = −σ(Dg) for Υ = −δ_F V, where
    σ(Φ) = ∫ X • Φ d‖V‖, X(x) = B_F(t(x)) and ‖V‖ = (H^k ⌞ M') ⌞ θ; by
    lem:first_variation and [dgpr_MS_transfer]. Direct formalisation. *)
Lemma dgpr_MS_constraint (t : RnM -> GA) (M' : set RnM) (theta : Rn -> R) :
  is_borel_function t ->
  V = measure_pushforward (fun x : RnM => ((x, t x) : GB)) W ->
  W = dgpr_main_measure k M' theta ->
  forall (g : smooth_test_space hE) (Dg : Rn -> Hom Rn Rn),
    (forall x, has_norm_differential Nn Nn setT (smooth_test_value hE g) x (Dg x)) ->
    is_measure_integral (dgpr_main_measure k M' theta)
      (real_total_integrand (fun x => HI (dgpr_B k F (set_val (t x) : Hom Rn Rn)) (Dg x)))
      (- (- S) g)%:E.
Proof.
move=> ht hVt hW g Dg hD.
have [c [hc hI]] := dgpr_first_variation hV.1 hVf hF.1 hD.
have e := dgpr_first_variation_unique (hS hD) hc.
have hg := dgpr_test_class_one hD.
have hI' := dgpr_MS_transfer ht hVt (dgpr_MS_test_integrand_borel hg) hI.
have e2 : (- S) g = - S g by [].
rewrite -hW e2 opprK e.
exact: hI'.
Qed.

(** Source for [dgpr_MS_reduction]: blueprint thm:MS, the proof up to
    the application of thm:main: by lem:KF, the data Y = R^n, K = K_F,
    λ(F), Λ(F), M', θ, X, Υ = −δ_F V and ‖Υ‖ = ν satisfy
    mr:hypotheses_main, where M' ⊆ M is a Borel set with
    ‖V‖ = (H^k ⌞ M') ⌞ θ. The blueprint uses M itself
    (docs/divergences.md). Direct formalisation. *)
Theorem dgpr_MS_reduction (l L : R) :
  is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
  exists (M' : set RnM) (theta : Rn -> R) (Xf : Rn -> Hom Rn Rn),
    [/\ M' `<=` dgpr_MS_set k W, W = dgpr_main_measure k M' theta &
      @dgpr_main_hypotheses R n k hk Rn _ hBn n (@coordinate_basis R n) E ev hE
        (dgpr_KF k F) l L M' theta Xf (- S) nu].
Proof.
move=> hl hL.
have [M' [hM'b hM'M hM'f]] := dgpr_MS_borel_part hV hVf hdens.
have hkn : (k <= n)%N by case/andP: hk.
have [t [ht _ hVt]] := allard_3_5_1_b_pushforward hkn hV.
have hW := dgpr_MS_weight_representation hV hVf hM'b hM'M hM'f.
have [hl0 hlL hKb] := dgpr_KF_bounds hF.1 hAC hl hL.
exists M', (dgpr_MS_density V M'), (fun x : Rn => dgpr_B k F (set_val (t x) : Hom Rn Rn)).
split=> //.
constructor.
- exact: hbn.
- exact: dgpr_KF_nonempty.
- exact: (dgpr_KF_compact_convex hF.1).1.
- exact: (dgpr_KF_compact_convex hF.1).2.
- exact: hl0.
- exact: lt_le_trans hl0 hlL.
- by move=> A hA; exact: (hKb A hA).1.
- by move=> A hA; exact: (hKb A hA).2.
- exact: hM'b.
- exact (dgpr_MS_rectifiable hV hVf hM'M).
- exact (dgpr_MS_borel_part_finite hV hVf hM'M).
- by move=> x _; exact: dgpr_MS_density_ge0.
- exact (dgpr_MS_density_summable hV hVf hM'b hM'M hM'f).
- by move=> x _; exact (dgpr_B_KF F (set_valP (t x))).
- apply: dgpr_borel_restrict_measurable.
  exact: (borel_function_composition ht (continuous_borel_function (dgpr_B_continuous hF.1))).
- exact: dgpr_MS_constraint ht hVt hW.
- exact: hnu.
- exact: hnur.
- move=> f hf; have [b [hb hbi]] := hnug hf.
  by exists b; split=> //; apply/dgpr_variation_value_opp.
- exact: hnuf.
Qed.

(** Source for [dgpr_theorem_1_6_from_main]: blueprint thm:MS, the
    conclusions (eq:MS:MS) and (eq:MS:sobolev) of DPGPR 2026, Theorem
    1.6, deduced from the conclusion of thm:main for λ(F), Λ(F) and a
    constant 0 ≤ C. The inequality for M' given by thm:main yields
    (eq:MS:MS) for M ⊇ M', since H^k(M') ≤ H^k(M) < ∞; combining it with
    (eq:MS:HM) and dividing by ‖V‖(R^n)^{1/k} gives (eq:MS:sobolev) if
    ‖V‖(R^n) > 0, and (eq:MS:sobolev) is trivial otherwise. Direct
    formalisation. *)
Theorem dgpr_theorem_1_6_from_main (C l L : R) :
  0 <= C -> is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
  dgpr_main_inequality hk l L C ->
  (W setT <= (C * real_power (fine (HK (dgpr_MS_set k W))) k%:R^-1)%:E * nu setT)%E /\
  ((1 < k)%N -> ((real_power (fine (W setT)) ((k%:R - 1) / k%:R))%:E <= C%:E * nu setT)%E).
Proof.
move=> hC hl hL hmain.
have [M' [theta [Xf [hM'M hW hH]]]] := dgpr_MS_reduction hl hL.
have [hm _ _ hWf] := dgpr_weight_laws hV hVf.
have [hHm _] := @hausdorff_measure_laws R n k.
have hHM : (HK (dgpr_MS_set k W) <= W setT)%E := dgpr_MS_HM hV hVf.
have hMf : (HK (dgpr_MS_set k W) < +oo)%E := le_lt_trans hHM hWf.
have hM'f : (HK M' < +oo)%E := dgpr_main_M_finite hH.
have hM'0 : (0 <= HK M')%E := measure_nonnegative hHm M'.
have hM0 : (0 <= HK (dgpr_MS_set k W))%E := measure_nonnegative hHm _.
have hnu0 : (0 <= nu setT)%E := measure_nonnegative hnu setT.
have hk0 : 0 < k%:R^-1 :> R by rewrite invr_gt0 ltr0n; case/andP: hk.
have hle : fine (HK M') <= fine (HK (dgpr_MS_set k W)).
  apply: fine_le; [by rewrite ge0_fin_numE | by rewrite ge0_fin_numE |].
  exact: (measure_mono hHm hM'M).
have hpow : real_power (fine (HK M')) k%:R^-1 <= real_power (fine (HK (dgpr_MS_set k W))) k%:R^-1.
  exact: (real_power_monotone (fine_ge0 hM'0) hle hk0).
have h1 := hmain _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH.
rewrite -hW in h1.
have hMS : (W setT <= (C * real_power (fine (HK (dgpr_MS_set k W))) k%:R^-1)%:E * nu setT)%E.
  apply: (le_trans h1); apply: lee_wpmul2r => //; rewrite lee_fin; by apply: ler_wpM2l.
split=> // hk1.
have hk0' : (k%:R : R) != 0 by rewrite pnatr_eq0 -lt0n; case/andP: hk.
have ek : (k%:R - 1) / k%:R + k%:R^-1 = 1 :> R by rewrite mulrBl mul1r subrK mulfV.
have hpos : 0 < (k%:R - 1) / k%:R :> R.
  by apply: divr_gt0; [rewrite subr_gt0 ltr1n | rewrite ltr0n; case/andP: hk].
have hW0 : (0 <= W setT)%E := measure_nonnegative hm setT.
have hWfin : W setT \is a fin_num by rewrite ge0_fin_numE.
have hnufin : nu setT \is a fin_num by rewrite ge0_fin_numE.
move: hMS; rewrite -[in X in (X <= _)%E](fineK hWfin) -(fineK hnufin) -EFinM lee_fin => hMS.
rewrite -(fineK hnufin) -EFinM lee_fin.
have hw0 : 0 <= fine (W setT) := fine_ge0 hW0.
have hq0 : 0 <= fine (nu setT) := fine_ge0 hnu0.
have hmw : fine (HK (dgpr_MS_set k W)) <= fine (W setT).
  by apply: fine_le => //; rewrite ge0_fin_numE.
have hp : real_power (fine (HK (dgpr_MS_set k W))) k%:R^-1 <= real_power (fine (W setT)) k%:R^-1.
  exact: (real_power_monotone (fine_ge0 hM0) hmw hk0).
have hMS' : fine (W setT) <= C * real_power (fine (W setT)) k%:R^-1 * fine (nu setT).
  apply: (le_trans hMS); apply: (ler_wpM2r hq0); by apply: ler_wpM2l.
have [hw|hw] := eqVneq (fine (W setT)) 0.
  rewrite hw real_power_zero_base; first exact: mulr_ge0 hC hq0.
  exact: lt0r_neq0 hpos.
have hwp : 0 < fine (W setT) by rewrite lt0r hw hw0.
have ha : 0 < real_power (fine (W setT)) k%:R^-1 := real_power_strictly_positive _ hwp.
rewrite -(ler_pM2r ha).
have e : real_power (fine (W setT)) ((k%:R - 1) / k%:R) * real_power (fine (W setT)) k%:R^-1 =
    fine (W setT).
  by rewrite -real_power_add_exponents_positive // ek real_power_one_exponent.
by rewrite e mulrAC.
Qed.

End MichaelSimon.

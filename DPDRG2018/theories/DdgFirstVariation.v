(** De Philippis, De Rosa and Ghiraldin (2018), Lemma A.2, (A.9), p. 1144,
    for an integrand F not depending on the point; blueprint ddg:A.2const.
    Let V be a d dimensional varifold in R^n of finite mass, let F be an
    integrand on G(n, d), and let g : R^n → R^n be of class 1 with
    Lip g ≤ K and |g| ≤ M. With φ_t(x) = x + t g(x) (DdgFlow.v), the
    anisotropic energy F(φ_t# V) = ∫ F(S) dφ_t# V(x, S) is finite for small
    |t|, (x, S) ↦ B_F(S) • Dg(x) is V summable, and

        d/dt F(φ_t# V) at t = 0 equals ∫ B_F(S) • Dg(x) dV(x, S).

    The image varifold φ_t# V is that of Allard 3.2, p. 430
    ([image_varifold]); its integrals are reduced to integrals with respect
    to V by Allard 3.2(1) ([allard_3_2_1_integral]). The derivative of the
    integrand at t = 0 is (A.8) ([ddg_weighted_jacobian_derivative]); the
    uniform estimate of DdgWeightedJacobianEstimate.v and Lebesgue's bounded
    convergence theorem, Federer 2.4.9, p. 85, justify differentiation
    under the integral sign. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal ring lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis TensorUP Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormDifferentialUP NormClassOneUP RelativeClassUP RelativeDifferentialUP NormRegularity
  NormClassOneCompactLipschitz NormCompactFunctionBound EuclideanClosedSupportTubeNorm NormMetric
  RealMetricBackground LipschitzUP NormMetricScaleContinuity RealCurveDerivativeUP
  ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci PartialAbsolutePartsGraph PartialDominatedConvergence MeasureUP
  MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureBoundedConvergence TotalExtendedLowerLimit
  MeasurableGraphEquivalence ExtendedConvergentLowerLimit ExtendedLowerLimitUP ExtendedLowerLimit
  SummableRealFunctionUP SummableRealArithmetic MeasureCharacteristicIntegral
  CharacteristicFunctionUP BorelFunctionUP BorelFunctionBasic BorelFiniteRealProduct
  MeasureAbsoluteSummability.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds AllardImageVarifold.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane DdgAnisotropicIntegrandUP
  DdgAnisotropicIntegrand DdgWeightedJacobian DdgWeightedJacobianEstimate DdgFlow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ddg_order_limit_real]: Federer 2.1.1, p. 51: a sequence
    of real numbers u converges to l in the order topology of the extended
    real numbers if |u(k) - l| < e for all large k, whenever e > 0.
    Supporting lemma. *)
Lemma ddg_order_limit_real (R : realType) (u : nat -> R) (l : R) :
  (forall e : R, 0 < e -> exists N : nat, forall k, (N <= k)%N -> `|u k - l| < e) ->
  extended_order_limit (fun k => (u k)%:E) l%:E.
Proof.
move=> h; split.
- case=> [r||] hr.
  + have he : 0 < l - r by rewrite subr_gt0 -lte_fin.
    have [N hN] := h _ he; exists N=> k hk; rewrite lte_fin.
    by have := hN k hk; rewrite ltr_norml=> /andP [h1 h2]; lra.
  + by rewrite ltNge leey in hr.
  + by exists 0%N=> k _; exact: ltNyr.
- case=> [r||] hr.
  + have he : 0 < r - l by rewrite subr_gt0 -lte_fin.
    have [N hN] := h _ he; exists N=> k hk; rewrite lte_fin.
    by have := hN k hk; rewrite ltr_norml=> /andP [h1 h2]; lra.
  + by exists 0%N=> k _; exact: ltry.
  + by rewrite ltNge leNye in hr.
Qed.

(** Source for [ddg_order_limit_realP]: Federer 2.1.1, p. 51: conversely,
    if u converges to l in the order topology of the extended real
    numbers and e > 0, then |u(k) - l| < e for all large k. Supporting
    lemma. *)
Lemma ddg_order_limit_realP (R : realType) (u : nat -> R) (l e : R) :
  extended_order_limit (fun k => (u k)%:E) l%:E -> 0 < e ->
  exists N : nat, forall k, (N <= k)%N -> `|u k - l| < e.
Proof.
move=> [hlow hup] he.
have hle : ((l - e)%:E < l%:E)%E by rewrite lte_fin; lra.
have hue : (l%:E < (l + e)%:E)%E by rewrite lte_fin; lra.
have [N1 h1] := hlow _ hle.
have [N2 h2] := hup _ hue.
exists (maxn N1 N2)=> k hk.
have := h1 k (leq_trans (leq_maxl _ _) hk); have := h2 k (leq_trans (leq_maxr _ _) hk).
rewrite !lte_fin=> hb ha.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [ddg_order_limit_eq]: a sequence equal termwise to a
    convergent one has the same limit, Federer 2.1.1, p. 51. Supporting
    lemma. *)
Lemma ddg_order_limit_eq (R : realType) (u v : nat -> \bar R) (l : \bar R) :
  (forall k, u k = v k) -> extended_order_limit u l -> extended_order_limit v l.
Proof. by move=> e h; have -> : v = u by apply: funext=> k; rewrite e. Qed.

(** Source for [ddg_sequence_small]: Archimedes: if 0 ≤ r and 0 < e, then
    r / (k + 1) < e for all large k. Supporting lemma. *)
Lemma ddg_sequence_small (R : realType) (r e : R) : 0 <= r -> 0 < e ->
  exists N : nat, forall k, (N <= k)%N -> r / k.+1%:R < e.
Proof.
move=> hr he.
have hq : 0 <= r / e by rewrite divr_ge0 // ltW.
exists (Num.Def.archi_bound (r / e))=> k hk.
have h1 := archi_boundP hq.
have h2 : (Num.Def.archi_bound (r / e))%:R <= k%:R :> R by rewrite ler_nat.
have hk1 : 0 < k.+1%:R :> R by rewrite ltr0Sn.
have h3 : r / e < k.+1%:R by rewrite -natr1; lra.
have h4 : r / e * e < k.+1%:R * e by rewrite ltr_pM2r.
rewrite divfK ?lt0r_neq0 // in h4.
have h5 : r / k.+1%:R * k.+1%:R = r by rewrite divfK // lt0r_neq0.
rewrite -(ltr_pM2r hk1) h5 mulrC; exact: h4.
Qed.

(** Source for [ddg_punctured_limit_sequence]: the sequential criterion
    for the limit of Federer 2.9.19, p. 163: if r > 0 and u(h(k)) converges
    to l for every sequence h with 0 < |h(k)| < r / (k + 1), then
    u(h) → l as h → 0, h ≠ 0. Supporting lemma. *)
Lemma ddg_punctured_limit_sequence (R : realType) (u : R -> R) (l r : R) : 0 < r ->
  (forall h : nat -> R, (forall k, 0 < `|h k| < r / k.+1%:R) ->
    extended_order_limit (fun k => (u (h k))%:E) l%:E) ->
  punctured_real_limit u l.
Proof.
move=> hr hseq; apply: contrapT=> hn.
have [e he hbad] : exists2 e : R, 0 < e & forall q : R, 0 < q ->
    exists x : R, 0 < `|x| < q /\ e <= `|u x - l|.
  apply: contrapT=> hno; apply: hn=> e he.
  apply: contrapT=> hnd; apply: hno; exists e=> // q hq.
  apply: contrapT=> hnx; apply: hnd; exists q; split=> // x hx.
  rewrite ltNge; apply/negP=> hle; apply: hnx; exists x; split.
  - exact: hx.
  - exact: hle.
have hpos k : 0 < r / k.+1%:R :> R by rewrite divr_gt0 // ltr0Sn.
have [h hh] := choice (fun k => hbad _ (hpos k)).
have [N hN] := ddg_order_limit_realP (hseq h (fun k => (hh k).1)) he.
have h1 := hN N (leqnn N); have h2 := (hh N).2; lra.
Qed.

(** Source for [ddg_dominated_integral_limit]: Lebesgue's bounded
    convergence theorem, Federer 2.4.9, p. 85, for real valued functions:
    if |f_k| ≤ H with H summable, f_k → β pointwise and ∫ f_k = a_k, then
    β is summable and a_k → ∫ β. The measurability of β follows from
    Federer 2.3.2(6)–(7), p. 74. Supporting lemma. *)
Lemma ddg_dominated_integral_limit (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (hm : is_measure mu) (f : nat -> X -> R) (beta H : X -> R) (a : nat -> R) :
  is_measure_summable mu (real_total_integrand H) ->
  (forall k x, `|f k x| <= H x) ->
  (forall x, extended_order_limit (fun k => (f k x)%:E) (beta x)%:E) ->
  (forall k, is_measure_integral mu (real_total_integrand (f k)) (a k)%:E) ->
  exists b : R, is_measure_integral mu (real_total_integrand beta) b%:E /\
    extended_order_limit (fun k => (a k)%:E) b%:E.
Proof.
move=> hH hb hc hi.
have hgraph (v : X -> R) x y : partial_function_graph (real_total_integrand v) x y <->
    partial_function_graph (partial_function_total (fun z => (v z)%:E : extended_real_line R)) x y.
  exact: real_total_integrand_graph.
have hf k : is_measure_measurable_function mu
    (partial_function_total (fun z => (f k z)%:E : extended_real_line R)).
  exact: (measurable_function_graph_equivalent (hgraph (f k)) (hi k).1).
have hlm := total_extended_lower_limit_measurable hm hf.
have hg : is_measure_measurable_function mu (real_total_integrand beta).
  apply: (measurable_function_graph_equivalent _ hlm)=> x y.
  have e : total_extended_lower_limit (fun k z => (f k z)%:E : extended_real_line R) x =
      (beta x)%:E.
    exact: (extended_lower_limit_unique (extended_lower_limit_laws _)
      (extended_convergent_lower_limit (hc x))).
  rewrite (hgraph beta x y); split=> h.
  - change ((beta x)%:E = y); rewrite -e; exact: h.
  - change (total_extended_lower_limit (fun k z => (f k z)%:E : extended_real_line R) x = y).
    rewrite e; exact: h.
have hdom k : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand (f k))) (real_total_integrand H)).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|f k x|)%:E, (H x)%:E; split.
  - exists (f k x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first exact/real_total_integrand_graph.
    by rewrite lee_fin; exact: hb.
have hconv : measure_almost_everywhere mu (partial_extended_convergence_locus
    (fun k => real_total_integrand (f k)) (real_total_integrand beta)).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun k => (f k x)%:E), (beta x)%:E; split.
  - by move=> k; exact/real_total_integrand_graph.
  - split; first exact/real_total_integrand_graph.
    exact: hc.
have [c [e [b [hci [hgi [_ [_ hlim]]]]]]] := measure_bounded_convergence hm hH
  (fun k => (hi k).1) hg hdom hconv.
have hca : c = a.
  apply: funext=> k; have hh := measure_integral_unique (hci k) (hi k); by case: hh.
by exists b; split=> //; rewrite -hca.
Qed.

Section FirstVariation.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).
Local Notation GA := (projection_grassmann R n d).
Local Notation GB := (grassmann_bundle R n d).

Variable V : set GB -> \bar R.
Hypothesis hV : is_varifold V.
Hypothesis hVfin : (V setT < +oo)%E.
Variable F : Hom Rn Rn -> R.
Variables (g : Rn -> Rn) (Dg : Rn -> Hom Rn Rn) (K M : R).
Hypothesis hg : is_norm_class_one_field Nn Nn setT g Dg.
Hypothesis hK0 : 0 <= K.
Hypothesis hK : forall y z, Nn (g y - g z) <= K * Nn (y - z).
Hypothesis hM : forall y, Nn (g y) <= M.

(** Source for [ddg_flow_integrand]: Allard 3.2(1), p. 430, applied to
    the function (x, S) ↦ F(S) and to φ_t: the integrand
    F(Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ of F(φ_t# V) with respect to V, where
    Dφ_t(x)(S) is the orthogonal projection onto Dφ_t(x)[im S].
    Definition. *)
Definition ddg_flow_integrand (t : R) (z : GB) : R :=
  F (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn) *
  image_bundle_jacobian (ddg_flow_differential Dg t) z.

(** Source for [ddg_flow_plane]: Allard 3.2, p. 430, and blueprint
    new:projection_formula: for |t| K < 1 the second component of
    (φ_t)_♮(x, S) is the orthogonal projection onto (1 + t Dg(x))[im S].
    Supporting lemma. *)
Lemma ddg_flow_plane (t : R) (z : GB) :
  `|t| * K < 1 ->
  is_ddg_plane_projection d (idn + t *: Dg z.1) (set_val z.2 : Hom Rn Rn)
    (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn).
Proof.
move=> htK; split; first exact: projection_grassmannP.
move=> y.
exact: (image_bundle_map_plane (ddg_flow g t) z y
  (fun x => ddg_flow_differential_injective (x := x) hg hK htK)).
Qed.

(** Source for [ddg_flow_integrand_zero]: φ_0 = 1_{R^n}, so the integrand
    at t = 0 is F(S). Supporting lemma. *)
Lemma ddg_flow_integrand_zero (z : GB) : ddg_flow_integrand 0 z = F (set_val z.2).
Proof.
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have h0 : `|0 : R| * K < 1 by rewrite normr0 mul0r ltr01.
have hP := ddg_flow_plane z h0.
rewrite /ddg_flow_integrand (ddg_plane_zero hT hP).
have -> : image_bundle_jacobian (ddg_flow_differential Dg 0) z = 1.
  rewrite /image_bundle_jacobian /ddg_flow_differential scale0r addr0.
  have -> : hom_comp idn (set_val z.2 : Hom Rn Rn) = set_val z.2.
    by apply: hom_ext=> x; rewrite hom_compE ddg_hom_idE.
  exact: ddg_jacobian_projection hT.
by rewrite mulr1.
Qed.

(** Source for [ddg_constant_summable]: a constant function is V
    summable, since V has finite mass, Federer 2.4.2–2.4.4, pp. 81–82.
    Supporting lemma. *)
Lemma ddg_constant_summable (b : R) : is_measure_summable V (real_total_integrand (fun _ : GB => b)).
Proof.
have hm := varifold_measure hV.
have hfn : V setT \is a fin_num by rewrite ge0_fin_numE // (measure_nonnegative hm setT).
have hc : is_characteristic_function [set: GB] (fun _ : GB => 1 : R).
  by split=> // x hx; exfalso; apply: hx.
have hi := measure_characteristic_integral hm hc (measure_measurable_whole hm).
rewrite -(fineK hfn) in hi.
have h := real_total_integral_scale hm b hi.
have e : (fun _ : GB => b * 1) = (fun _ : GB => b) by apply: funext=> x; rewrite mulr1.
by rewrite e in h; exists (b * fine (V setT)).
Qed.

(** Source for [ddg_bounded_summable]: a bounded real valued Borel
    function on G_d(R^n) is V summable, since V has finite mass, Federer
    2.4.4(6), p. 82, and 2.4.9, p. 85. Supporting lemma. *)
Lemma ddg_bounded_summable (f : GB -> R) (b : R) :
  is_borel_function (f : GB -> real_line_metric R) -> (forall z, `|f z| <= b) ->
  exists a : R, is_measure_integral V (real_total_integrand f) a%:E.
Proof.
move=> hf hb.
have hm := varifold_measure hV.
have hmeas := varifold_borel_measurable hV hf.
have hdom : measure_almost_everywhere V (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand f))
    (real_total_integrand (fun _ : GB => b))).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|f x|)%:E, b%:E; split.
  - exists (f x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first exact/real_total_integrand_graph.
    by rewrite lee_fin.
exact: (measure_dominated_summable hm hmeas (ddg_constant_summable b) hdom).1.
Qed.

Section Constants.
Variables Lam Phi : R.
Hypothesis hLam : 0 <= Lam.
Hypothesis hFL : forall S S', G S -> G S' -> `|F S - F S'| <= Lam * NH (S - S').
Hypothesis hFb : forall S, G S -> `|F S| <= Phi.
Hypothesis hFd : forall T, G T -> ddg_relative_differentiable_at d F T.

(** Source for [ddg_integrand_continuous]: an integrand which is
    Lipschitz on G(n, d) is continuous on G(n, d) with the metric of
    Allard 2.2. Supporting lemma. *)
Lemma ddg_integrand_continuous :
  continuous (fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)).
Proof.
apply: (metric_fixed_lipschitz_continuous (L := Lam) hLam)=> S S'.
rewrite real_line_metric_distanceE projection_grassmann_distanceE.
exact: hFL (projection_grassmannP S) (projection_grassmannP S').
Qed.

(** Source for [ddg_integrand_borel]: (x, S) ↦ F(S) is a Borel function
    on G_d(R^n). Supporting lemma. *)
Lemma ddg_integrand_borel :
  is_borel_function ((fun z : GB => F (set_val z.2 : Hom Rn Rn)) : GB -> real_line_metric R).
Proof.
have hc : continuous (fun z : GB => (F (set_val z.2 : Hom Rn Rn) : real_line_metric R)).
  exact: (continuous_function_composition (@grassmann_bundle_plane_continuous R n d) ddg_integrand_continuous).
exact: (continuous_borel_function hc).
Qed.

(** Source for [ddg_flow_integrand_borel]: Allard 3.2, p. 430: for
    |t| K < 1 the integrand of F(φ_t# V) is continuous, hence Borel, on
    G_d(R^n). Supporting lemma. *)
Lemma ddg_flow_integrand_borel (t : R) :
  `|t| * K < 1 -> is_borel_function ((ddg_flow_integrand t) : GB -> real_line_metric R).
Proof.
move=> htK.
have hinj x : injective (ddg_flow_differential Dg t x).
  exact: (ddg_flow_differential_injective hg hK htK).
have hc2 : continuous (fun z : GB =>
    (F (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn)
      : real_line_metric R)).
  have h1 := @image_bundle_map_continuous R n d _ _ (ddg_flow_class_one hg t) hinj.
  have h2 := continuous_function_composition (@grassmann_bundle_plane_continuous R n d)
    ddg_integrand_continuous.
  exact: (continuous_function_composition h1 h2).
have hc3 := @image_bundle_jacobian_continuous R n d _ _ (ddg_flow_class_one hg t).
exact: (borel_finite_real_product (continuous_borel_function hc2) (continuous_borel_function hc3)).
Qed.

(** Source for [ddg_flow_integrand_derivative]: DDG (A.8), p. 1144:
    d/dt F(Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ at t = 0 equals B_F(S) • Dg(x).
    Supporting lemma. *)
Lemma ddg_flow_integrand_derivative (z : GB) :
  has_real_curve_derivative (fun t => ddg_flow_integrand t z) 0
    (HI (ddg_B d F (set_val z.2 : Hom Rn Rn)) (Dg z.1)).
Proof.
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have hB := ddg_B_spec hT (hFd hT).
have hP : exists2 delta : R, 0 < delta & forall t, `|t| < delta ->
    is_ddg_plane_projection d (idn + t *: Dg z.1) (set_val z.2 : Hom Rn Rn)
      (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn).
  have hK1 : 0 < K + 1 by have := hK0; lra.
  exists (1 / (K + 1)); first by rewrite divr_gt0.
  move=> t ht; apply: ddg_flow_plane.
  have h1 : `|t| * (K + 1) < 1 / (K + 1) * (K + 1) by rewrite ltr_pM2r.
  rewrite divfK ?lt0r_neq0 // in h1.
  have h2 := normr_ge0 t; nra.
exact: (@ddg_weighted_jacobian_derivative R n d F _ _ (Dg z.1) _ hT hB hP).
Qed.

(** Source for [ddg_flow_integrand_estimate]: proof of DDG Lemma A.2,
    p. 1144: |F(Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ - F(S)| ≤ C |t| with
    C = 2^d (3 n^{1/2} Λ + Φ) n^{1/2} K, whenever |t| K < 1 and
    |t| n^{1/2} K ≤ 1/2. Supporting lemma. *)
Lemma ddg_flow_integrand_estimate (t : R) (z : GB) :
  `|t| * K < 1 -> `|t| * (Num.sqrt n%:R * K) <= 1 / 2 ->
  `|ddg_flow_integrand t z - ddg_flow_integrand 0 z| <=
    2 ^+ d * (3 * Num.sqrt n%:R * Lam + Phi) * (Num.sqrt n%:R * K) * `|t|.
Proof.
move=> htK hts.
rewrite ddg_flow_integrand_zero.
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have hP := ddg_flow_plane z htK.
have hL : NH (Dg z.1) <= Num.sqrt n%:R * K.
  apply: ddg_hom_norm_from_vector_bound=> // v.
  exact: (ddg_flow_differential_bound hg z.1 v hK).
have hs : NH (Dg z.1) * `|t| <= 1 / 2.
  apply: (le_trans (ler_wpM2r (normr_ge0 t) hL)); by rewrite mulrC.
have h := ddg_weighted_jacobian_estimate hLam hFL hFb hT hP hs.
apply: (le_trans h).
have hPhi : 0 <= Phi := le_trans (normr_ge0 _) (hFb hT).
have hA : 0 <= 2 ^+ d * (3 * Num.sqrt n%:R * Lam + Phi).
  by rewrite mulr_ge0 ?exprn_ge0 // addr_ge0 // mulr_ge0 // mulr_ge0 // sqrtr_ge0.
rewrite -[X in _ <= X]mulrA; apply: ler_wpM2l=> //.
by rewrite mulrC; apply: ler_wpM2r.
Qed.

(** Source for [ddg_lemma_A_2_constant_lipschitz]: DDG Lemma A.2, (A.9),
    p. 1144, for an integrand F not depending on the point which is
    Lipschitz and bounded on G(n, d) and differentiable relative to
    G(n, d) at every point of G(n, d): there are δ > 0 and c such that
    c = ∫ B_F(S) • Dg(x) dV(x, S), F(φ_t# V) is finite for |t| < δ, and
    d/dt F(φ_t# V) = c at t = 0. Direct formalisation, with the
    hypotheses stated in the module header. *)
Theorem ddg_lemma_A_2_constant_lipschitz :
  exists delta c : R, [/\ 0 < delta,
    is_measure_integral V
      (real_total_integrand (fun z : GB => HI (ddg_B d F (set_val z.2 : Hom Rn Rn)) (Dg z.1))) c%:E,
    forall t, `|t| < delta -> exists a : R,
      is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
        (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta ->
        is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
          (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
have hm := varifold_measure hV.
pose sK := Num.sqrt n%:R * K.
have hsK : 0 <= sK by rewrite mulr_ge0 // sqrtr_ge0.
pose s := sK + K + 1.
have hs : 0 < s by rewrite /s; have := hK0; lra.
pose delta := 1 / (2 * s).
have hdelta : 0 < delta by rewrite /delta divr_gt0 // mulr_gt0.
have hdt (t : R) : `|t| < delta -> `|t| * K < 1 /\ `|t| * sK <= 1 / 2.
  move=> ht.
  have h2s : 0 < 2 * s by rewrite mulr_gt0.
  have h1 : `|t| * (2 * s) < delta * (2 * s) by rewrite ltr_pM2r.
  rewrite /delta divfK ?lt0r_neq0 // in h1.
  have h2 := normr_ge0 t.
  have h3 : 0 <= `|t| * sK by rewrite mulr_ge0.
  have h4 : 0 <= `|t| * K by rewrite mulr_ge0.
  rewrite /s in h1; split; nra.
pose C := 2 ^+ d * (3 * Num.sqrt n%:R * Lam + Phi) * sK.
have hbound (t : R) (z : GB) : `|t| < delta -> `|ddg_flow_integrand t z - ddg_flow_integrand 0 z| <= C * `|t|.
  by move=> ht; have [h1 h2] := hdt t ht; exact: ddg_flow_integrand_estimate.
have hzero (z : GB) : `|ddg_flow_integrand 0 z| <= Phi.
  by rewrite ddg_flow_integrand_zero; exact: (hFb (projection_grassmannP z.2)).
have hint (t : R) : `|t| < delta -> exists a : R,
    is_measure_integral V (real_total_integrand (ddg_flow_integrand t)) a%:E.
  move=> ht; apply: (@ddg_bounded_summable _ (Phi + C * `|t|)).
    exact: (ddg_flow_integrand_borel (hdt t ht).1).
  move=> z; have h1 := hbound t z ht; have h2 := hzero z.
  have h3 := ler_normD (ddg_flow_integrand t z - ddg_flow_integrand 0 z) (ddg_flow_integrand 0 z).
  rewrite subrK in h3; lra.
have himm (t : R) : `|t| < delta ->
    is_proper_class_one_immersion (ddg_flow g t) (ddg_flow_differential Dg t).
  by move=> ht; exact: (ddg_flow_immersion hg hK hK0 hM (hdt t ht).1).
have hsmall (h : nat -> R) (k : nat) : (forall k, 0 < `|h k| < delta / k.+1%:R) -> `|h k| < delta.
  move=> hh; have /andP [_ h1] := hh k.
  apply: (lt_le_trans h1); rewrite ler_pdivrMr ?ltr0Sn //.
  have hk1 : (1 : R) <= k.+1%:R by rewrite ler1n.
  have := hdelta; nra.
have hlimit (h : nat -> R) (I0 : R) (Ih : nat -> R) :
    (forall k, 0 < `|h k| < delta / k.+1%:R) ->
    is_measure_integral V (real_total_integrand (ddg_flow_integrand 0)) I0%:E ->
    (forall k, is_measure_integral V (real_total_integrand (ddg_flow_integrand (h k))) (Ih k)%:E) ->
    exists b : R,
      is_measure_integral V
        (real_total_integrand (fun z : GB => HI (ddg_B d F (set_val z.2 : Hom Rn Rn)) (Dg z.1))) b%:E /\
      extended_order_limit (fun k => ((h k)^-1 * (Ih k - I0))%:E) b%:E.
  move=> hh hI0 hIh.
  apply: (ddg_dominated_integral_limit hm
    (f := fun k z => (h k)^-1 * (ddg_flow_integrand (h k) z - ddg_flow_integrand 0 z))
    (H := fun _ => C)).
  - exact: ddg_constant_summable.
  - move=> k z.
    have /andP [hp _] := hh k.
    have hb := hbound (h k) z (hsmall h k hh).
    rewrite normrM normfV.
    have hi : 0 <= `|h k|^-1 by rewrite invr_ge0 ltW.
    apply: (le_trans (ler_wpM2l hi hb)).
    by rewrite mulrCA mulVf ?mulr1 // lt0r_neq0.
  - move=> z; apply: ddg_order_limit_real=> e he.
    have [r [hr hder]] := (@ddg_flow_integrand_derivative z) e he.
    have [N hN] := ddg_sequence_small (ltW hdelta) hr.
    exists N=> k hk.
    have /andP [hp hq] := hh k.
    have hhr : 0 < `|h k| < r by rewrite hp (lt_trans hq (hN k hk)).
    have := hder (h k) hhr.
    by rewrite add0r mulrC.
  - move=> k.
    exact: (real_total_integral_scale hm (h k)^-1 (real_total_integral_subtract hm (hIh k) hI0)).
have halpha := ddg_integrand_borel.
have h00 : `|0 : R| < delta by rewrite normr0.
have [I0 hI0] := hint 0 h00.
pose h0 (k : nat) := delta / k.+1%:R / 2.
have hh0 k : 0 < `|h0 k| < delta / k.+1%:R.
  have hp : 0 < delta / k.+1%:R by rewrite divr_gt0 // ltr0Sn.
  have hq : 0 < h0 k by rewrite /h0 divr_gt0.
  rewrite gtr0_norm // hq /= /h0.
  by move: (delta / k.+1%:R) hp=> q hpq; lra.
have [Ih hIh] := choice (fun k => hint (h0 k) (hsmall h0 k hh0)).
have [c [hc _]] := hlimit h0 I0 Ih hh0 hI0 hIh.
exists delta, c; split=> //.
- move=> t ht; have [a ha] := hint t ht; exists a.
  exact/(allard_3_2_1_integral hV (himm t ht) halpha a%:E).
- move=> I hI.
  apply: (@ddg_punctured_limit_sequence _ _ _ delta hdelta)=> h hh.
  have hI0' : is_measure_integral V (real_total_integrand (ddg_flow_integrand 0)) (I 0)%:E.
    exact/(allard_3_2_1_integral hV (himm 0 h00) halpha _).1/(hI 0 h00).
  have hIh' k : is_measure_integral V (real_total_integrand (ddg_flow_integrand (h k))) (I (h k))%:E.
    have hk := hsmall h k hh.
    exact/(allard_3_2_1_integral hV (himm _ hk) halpha _).1/(hI _ hk).
  have [b [hb hlim]] := hlimit h (I 0) (fun k => I (h k)) hh hI0' hIh'.
  have ebc : b = c by apply: EFin_inj; exact: (measure_integral_unique hb hc).
  rewrite -ebc; apply: (ddg_order_limit_eq _ hlim)=> k /=.
  by rewrite add0r mulrC.
Qed.

End Constants.

(** Source for [ddg_integrand_relative_class]: Federer 3.1.22, p. 236: an
    integrand of class 1 on an open set W ⊇ G(n, d) is of class 1 relative
    to G(n, d). Supporting lemma. *)
Lemma ddg_integrand_relative_class (W : set (Hom Rn Rn)) :
  norm_class_one NH N1 W F -> G `<=` W -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1.
Proof.
move=> hF hGW a ha; exists W, F; split; first exact: hGW.
split; first exact: (norm_class_firstP hNH hN1 W F).2 hF.
by move=> x hx _; split.
Qed.

(** Source for [ddg_integrand_lipschitz]: Federer 3.1.1, p. 209, and
    Allard 2.3: an integrand of class 1 on an open set W ⊇ G(n, d) is
    Lipschitz on the compact set G(n, d). Supporting lemma. *)
Lemma ddg_integrand_lipschitz (W : set (Hom Rn Rn)) :
  norm_class_one NH N1 W F -> G `<=` W ->
  exists2 Lam : R, 0 <= Lam & forall S S', G S -> G S' -> `|F S - F S'| <= Lam * NH (S - S').
Proof.
move=> hF hGW.
have hG : @compact (real_norm_metric_space hNH) G.
  exact: (inner_norm_compact_topology_iff (hom_inner_productP hBn hBn hbn) G).1
    (@orthogonal_projectors_compact R n d).
have [Lam [hLam [_ hL]]] := norm_class_one_compact_lipschitz hN1 hF hGW hG.
exists Lam; first exact: ltW.
move=> S S' hS hS'; have := hL S S' hS hS'.
by rewrite !real_norm_metric_distanceE.
Qed.

(** Source for [ddg_integrand_bounded]: Federer 3.1.1, p. 210, and
    Allard 2.3: an integrand of class 1 on an open set W ⊇ G(n, d) is
    bounded on the compact set G(n, d). Supporting lemma. *)
Lemma ddg_integrand_bounded (W : set (Hom Rn Rn)) :
  norm_class_one NH N1 W F -> G `<=` W -> exists Phi : R, forall S, G S -> `|F S| <= Phi.
Proof.
move=> [D hD] hGW.
have hG : @compact (real_norm_metric_space hNH) G.
  exact: (inner_norm_compact_topology_iff (hom_inner_productP hBn hBn hbn) G).1
    (@orthogonal_projectors_compact R n d).
have [Phi [_ hPhi]] := norm_class_zero_compact_bounded hN1 hG hGW
  (norm_class_one_zero hD).
by exists Phi.
Qed.

(** Source for [ddg_lemma_A_2_constant]: DDG Lemma A.2, (A.9), p. 1144;
    blueprint ddg:A.2const: if V is a d dimensional varifold in R^n of
    finite mass, F is of class 1 on an open set W ⊇ G(n, d), g is of class
    1 with Lip g ≤ K and |g| ≤ M, and φ_t(x) = x + t g(x), then for some
    δ > 0 the energy F(φ_t# V) = ∫ F(S) dφ_t# V(x, S) is finite for
    |t| < δ, (x, S) ↦ B_F(S) • Dg(x) is V summable, and
    d/dt F(φ_t# V) at t = 0 equals ∫ B_F(S) • Dg(x) dV(x, S). Direct
    formalisation. *)
Theorem ddg_lemma_A_2_constant (W : set (Hom Rn Rn)) :
  norm_class_one NH N1 W F -> G `<=` W ->
  exists delta c : R, [/\ 0 < delta,
    is_measure_integral V
      (real_total_integrand (fun z : GB => HI (ddg_B d F (set_val z.2 : Hom Rn Rn)) (Dg z.1))) c%:E,
    forall t, `|t| < delta -> exists a : R,
      is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
        (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta ->
        is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
          (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
move=> hF hGW.
have [Lam hLam hFL] := ddg_integrand_lipschitz hF hGW.
have [Phi hFb] := ddg_integrand_bounded hF hGW.
have hrel := ddg_integrand_relative_class hF hGW.
exact: (ddg_lemma_A_2_constant_lipschitz hLam hFL hFb
  (fun T hT => ddg_relative_differentiable hT hrel)).
Qed.

End FirstVariation.

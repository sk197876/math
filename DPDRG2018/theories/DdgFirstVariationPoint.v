(** De Philippis, De Rosa and Ghiraldin (2018), Lemma A.2, (A.8), p. 1144;
    blueprint ddg:A.2. Let V be a d dimensional varifold in R^n, let
    F : R^n × Hom(R^n, R^n) → R be of class 1 on an open set U containing
    R^n × G(n, d), and let g : R^n → R^n be of class 1 with Lip g ≤ K,
    |g| ≤ M, and g(y) = 0, Dg(y) = 0 whenever |y| ≥ ρ. With
    φ_t(x) = x + t g(x) (DdgFlow.v) and B_F(x, S) the matrix of
    def:BF for the frozen integrand F(x, ·), the function
    (x, S) ↦ D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x) is V summable, and

        d/dt F(φ_t# V) at t = 0 equals
        ∫ D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x) dV(x, S)

    in the following sense: for small |t| the function
    (x, S) ↦ F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ - F(x, S) is
    V summable, its integral has the stated derivative at t = 0, and, when
    F(V) is finite, so is F(φ_t# V), and the derivative of F(φ_t# V) at
    t = 0 is the stated integral. The product R^n × Hom(R^n, R^n) carries
    the inner product of Federer 1.7.11, p. 36 ([product_inner]); the
    partial differential D_x F(x, S)(v) is DF(x, S)(v, 0). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology normedtype constructive_ereal ring lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis TensorUP Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormDifferentialUP NormClassOneUP RelativeClassUP RelativeDifferentialUP NormRegularity
  NormClassOneCompactLipschitz NormCompactFunctionBound EuclideanClosedSupportTubeNorm NormMetric
  RealMetricBackground LipschitzUP NormMetricScaleContinuity RealCurveDerivativeUP
  RealCurveDerivativeLaws PuncturedRealLinearLimits RealCurvePolynomialDerivatives
  NormedCurveDerivativeUP
  ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  SummableRealArithmetic MeasureCharacteristicIntegral CharacteristicFunctionUP BorelFunctionUP
  BorelFunctionBasic MeasureAbsoluteSummability ProductInner ProductInnerPairRegularity
  ProductInnerNormBounds InnerCartesianContinuousMaps InnerOwnNormTopology HomeomorphismUP
  NormClassZeroTopology TopologicalProductMaps MetricSubsetBackground EuclideanClosedBallCompact
  MetricClosedBalls InnerNormInequalities EuclideanLinearJacobian RadonMeasureUP MeasureBasic.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds AllardImageVarifoldMaps AllardImageVarifold.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane DdgLemmaA1
  DdgGrassmannTangent DdgAnisotropicIntegrandUP DdgAnisotropicIntegrand DdgWeightedJacobian
  DdgWeightedJacobianEstimate DdgFlow DdgFirstVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ddg_real_curve_derivative_add]: Federer 2.9.19, p. 163:
    (f + g)'(x) = f'(x) + g'(x). Supporting lemma. *)
Lemma ddg_real_curve_derivative_add (R : realType) (f g : R -> R) (x a b : R) :
  has_real_curve_derivative f x a -> has_real_curve_derivative g x b ->
  has_real_curve_derivative (fun t => f t + g t) x (a + b).
Proof.
move=> hf hg; have h := punctured_real_limit_add hf hg.
apply: (punctured_real_limit_congr _ h)=> h0 _ /=.
by rewrite -mulrDl; congr (_ * _); ring.
Qed.

(** Source for [ddg_integral_derivative]: differentiation under the
    integral sign, from Lebesgue's bounded convergence theorem, Federer
    2.4.9, p. 85: if H(t, ·) - H(0, ·) is μ measurable and bounded by
    |t| w with w μ summable for |t| < δ, and β(x) is the derivative of
    t ↦ H(t, x) at 0 for every x, then β is μ summable, and every function
    I with I(t) = ∫ H(t, x) - H(0, x) dμ(x) for |t| < δ has derivative
    ∫ β dμ at 0. Supporting lemma. *)
Lemma ddg_integral_derivative (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (hm : is_measure mu) (H : R -> X -> R) (beta w : X -> R) (delta : R) :
  0 < delta -> is_measure_summable mu (real_total_integrand w) ->
  (forall t, `|t| < delta ->
    is_measure_measurable_function mu (real_total_integrand (fun x => H t x - H 0 x))) ->
  (forall t x, `|t| < delta -> `|H t x - H 0 x| <= `|t| * w x) ->
  (forall x, has_real_curve_derivative (fun t => H t x) 0 (beta x)) ->
  exists c : R, [/\ is_measure_integral mu (real_total_integrand beta) c%:E,
    forall t, `|t| < delta -> exists a : R,
      is_measure_integral mu (real_total_integrand (fun x => H t x - H 0 x)) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta ->
        is_measure_integral mu (real_total_integrand (fun x => H t x - H 0 x)) (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
move=> hdelta [aw hw] hmeas hdom hder.
have hint (t : R) : `|t| < delta -> exists a : R,
    is_measure_integral mu (real_total_integrand (fun x => H t x - H 0 x)) a%:E.
  move=> ht.
  have hmw := real_total_integral_scale hm `|t| hw.
  have hd : measure_almost_everywhere mu (partial_extended_le_locus
      (partial_extended_function_absolute_value (real_total_integrand (fun x => H t x - H 0 x)))
      (real_total_integrand (fun x => `|t| * w x))).
    apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
    exists (`|H t x - H 0 x|)%:E, (`|t| * w x)%:E; split.
    - exists (H t x - H 0 x)%:E; split; first exact/real_total_integrand_graph.
      by rewrite abse_EFin.
    - split; first exact/real_total_integrand_graph.
      by rewrite lee_fin; exact: hdom.
  have hs : is_measure_summable mu (real_total_integrand (fun x => `|t| * w x)).
    by exists (`|t| * aw).
  exact: (measure_dominated_summable hm (hmeas t ht) hs hd).1.
have hsmall (h : nat -> R) (k : nat) : (forall k, 0 < `|h k| < delta / k.+1%:R) -> `|h k| < delta.
  move=> hh; have /andP [_ h1] := hh k.
  apply: (lt_le_trans h1); rewrite ler_pdivrMr ?ltr0Sn //.
  have hk1 : (1 : R) <= k.+1%:R by rewrite ler1n.
  have := hdelta; nra.
have hlimit (h : nat -> R) (Ih : nat -> R) :
    (forall k, 0 < `|h k| < delta / k.+1%:R) ->
    (forall k, is_measure_integral mu (real_total_integrand (fun x => H (h k) x - H 0 x)) (Ih k)%:E) ->
    exists b : R, is_measure_integral mu (real_total_integrand beta) b%:E /\
      extended_order_limit (fun k => ((h k)^-1 * Ih k)%:E) b%:E.
  move=> hh hIh.
  apply: (ddg_dominated_integral_limit hm
    (f := fun k x => (h k)^-1 * (H (h k) x - H 0 x)) (H := w)).
  - by exists aw.
  - move=> k x.
    have /andP [hp _] := hh k.
    have hb := hdom (h k) x (hsmall h k hh).
    rewrite normrM normfV.
    have hi : 0 <= `|h k|^-1 by rewrite invr_ge0 ltW.
    apply: (le_trans (ler_wpM2l hi hb)).
    by rewrite mulrA mulVf ?mul1r // lt0r_neq0.
  - move=> x; apply: ddg_order_limit_real=> e he.
    have [r [hr hd]] := hder x e he.
    have [N hN] := ddg_sequence_small (ltW hdelta) hr.
    exists N=> k hk.
    have /andP [hp hq] := hh k.
    have hhr : 0 < `|h k| < r by rewrite hp (lt_trans hq (hN k hk)).
    have := hd (h k) hhr.
    by rewrite add0r mulrC.
  - move=> k; exact: (real_total_integral_scale hm (h k)^-1 (hIh k)).
have h00 : `|0 : R| < delta by rewrite normr0.
pose h0 (k : nat) := delta / k.+1%:R / 2.
have hh0 k : 0 < `|h0 k| < delta / k.+1%:R.
  have hp : 0 < delta / k.+1%:R by rewrite divr_gt0 // ltr0Sn.
  have hq : 0 < h0 k by rewrite /h0 divr_gt0.
  rewrite gtr0_norm // hq /= /h0.
  by move: (delta / k.+1%:R) hp=> q hpq; lra.
have [Ih hIh] := choice (fun k => hint (h0 k) (hsmall h0 k hh0)).
have [c [hc _]] := hlimit h0 Ih hh0 hIh.
exists c; split=> //.
move=> I hI.
have hI0 : I 0 = 0.
  have h1 := hI 0 h00.
  have h2 := real_total_integral_scale hm 0 hw.
  have e : (fun x => 0 * w x) = (fun x => H 0 x - H 0 x).
    by apply: funext=> x; rewrite mul0r subrr.
  rewrite e mul0r in h2.
  by apply: EFin_inj; exact: (measure_integral_unique h1 h2).
apply: (@ddg_punctured_limit_sequence _ _ _ delta hdelta)=> h hh.
have hIh' k : is_measure_integral mu (real_total_integrand (fun x => H (h k) x - H 0 x))
    (I (h k))%:E.
  exact: hI _ (hsmall h k hh).
have [b [hb hlim]] := hlimit h (fun k => I (h k)) hh hIh'.
have ebc : b = c by apply: EFin_inj; exact: (measure_integral_unique hb hc).
rewrite -ebc; apply: (ddg_order_limit_eq _ hlim)=> k /=.
by rewrite add0r hI0 subr0 mulrC.
Qed.

Section FirstVariationPoint.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hHI := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hHI).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).
Local Notation GA := (projection_grassmann R n d).
Local Notation GB := (grassmann_bundle R n d).
Local Notation XP := (Rn * Hom Rn Rn)%type.
Local Notation hX := (product_inner_productP hBn hHI).
Local Notation NX := (inner_norm hX).
Local Notation hNX := (inner_norm_real_norm hX).
Local Notation inj1 := (@product_first_injection_hom R Rn (Hom Rn Rn)).
Local Notation inj2 := (@product_second_injection_hom R Rn (Hom Rn Rn)).

Variable V : set GB -> \bar R.
Hypothesis hV : is_varifold V.
Variables (F : XP -> R^o) (DF : XP -> Hom XP R^o) (U : set XP).
Hypothesis hF : is_norm_class_one_field NX N1 U F DF.
Hypothesis hU : forall (x : Rn) (S : Hom Rn Rn), G S -> U (x, S).
Variables (g : Rn -> Rn) (Dg : Rn -> Hom Rn Rn) (K M rho : R).
Hypothesis hg : is_norm_class_one_field Nn Nn setT g Dg.
Hypothesis hK0 : 0 <= K.
Hypothesis hK : forall y z, Nn (g y - g z) <= K * Nn (y - z).
Hypothesis hM : forall y, Nn (g y) <= M.
Hypothesis hsupp : forall y, rho <= Nn y -> g y = 0 /\ Dg y = 0.

(** Source for [ddg_pair_shift]: Federer 1.7.11, p. 36: in
    R^n × Hom(R^n, R^n), (x, S) + (0, h) = (x, S + h). Supporting
    lemma. *)
Lemma ddg_pair_shift (x : Rn) (S h : Hom Rn Rn) : ((x, S) : XP) + inj2 h = (x, S + h).
Proof. by change ((x + 0, S + h) = (x, S + h)); rewrite addr0. Qed.

(** Source for [ddg_pair_norm]: Federer 1.7.11, p. 36: the norm of the
    product inner product satisfies |(a, b)| ≤ |a| + |b|. Supporting
    lemma. *)
Lemma ddg_pair_norm (a : Rn) (b : Hom Rn Rn) : NX ((a, b) : XP) <= Nn a + NH b.
Proof.
have e : ((a, b) : XP) = inj1 a + inj2 b.
  by change ((a, b) = (a + 0, 0 + b)); rewrite addr0 add0r.
rewrite e; apply: (le_trans (inner_norm_triangle hX _ _)).
rewrite product_first_injection_norm product_second_injection_norm; exact: lexx.
Qed.

(** Source for [ddg_frozen_class_one]: Federer 3.1.1, p. 209–210: if F
    is of class 1 on U, then the frozen integrand S ↦ F(x, S) is of class
    1 on {S : (x, S) ∈ U}, with differential h ↦ DF(x, S)(0, h).
    Supporting lemma. *)
Lemma ddg_frozen_class_one (x : Rn) :
  is_norm_class_one_field NH N1 (fun S => U (x, S)) (fun S => F (x, S))
    (fun S => hom_comp (DF (x, S)) inj2).
Proof.
have hz := norm_class_one_zero hF.
have hdiff := norm_class_one_differential hF.
have hcont := norm_class_one_continuity hF.
have hint S : U (x, S) -> norm_domain_interior NH (fun S => U (x, S)) S.
  move=> hS; have [[r [hr hr']] _] := hz _ hS.
  exists r; split=> // h hh.
  have := hr' (inj2 h); rewrite product_second_injection_norm ddg_pair_shift=> H; exact: H hh.
split.
- move=> S hS; split; first exact: hint.
  move=> e he; have [_ hc] := hz _ hS; have [d0 [hd0 hd]] := hc e he.
  exists d0; split=> // h hUh hh.
  have := hd (inj2 h); rewrite product_second_injection_norm ddg_pair_shift=> H; exact: H hUh hh.
- move=> S hS; have hD := hdiff _ hS; split.
  + exact: hint.
  + have [C [hC hCb]] := norm_differential_bounded hD; exists C; split=> // h.
    rewrite hom_compE; have := hCb (inj2 h); by rewrite product_second_injection_norm.
  + move=> e he; have [d0 [hd0 hd]] := norm_differential_remainder hD he.
    exists d0; split=> // h hUh hh; rewrite hom_compE.
    have := hd (inj2 h); rewrite product_second_injection_norm ddg_pair_shift=> H; exact: H hUh hh.
- move=> S hS e he; have [d0 [hd0 hd]] := hcont _ hS e he.
  exists d0; split=> // h hUh hh v.
  have := hd (inj2 h); rewrite product_second_injection_norm ddg_pair_shift=> H.
  have := H hUh hh (inj2 v); rewrite product_second_injection_norm; exact.
Qed.

(** Source for [ddg_frozen_differentiable]: Federer 3.1.22, p. 236, and
    def:BF: the frozen integrand S ↦ F(x, S) is differentiable at every
    T ∈ G(n, d) relative to G(n, d). Supporting lemma. *)
Lemma ddg_frozen_differentiable (x : Rn) (T : Hom Rn Rn) :
  G T -> ddg_relative_differentiable_at d (fun S => F (x, S)) T.
Proof.
move=> hT; apply: (ddg_relative_differentiable hT)=> a ha.
exists (fun S => U (x, S)), (fun S => F (x, S)); split; first exact: hU ha.
split; first exact: (norm_class_firstP hNH hN1 _ _).2 (ex_intro _ _ (ddg_frozen_class_one x)).
by move=> y hy _; split.
Qed.

(** Source for [ddg_pair_curve_derivative]: Federer 2.9.22, p. 164, in
    R^n × Hom(R^n, R^n): if P'(0) = T', then the curve
    t ↦ (x + t v, P(t)) has derivative (v, T') at 0. Supporting lemma. *)
Lemma ddg_pair_curve_derivative (x v : Rn) (P : R -> Hom Rn Rn) (T' : Hom Rn Rn) :
  has_normed_curve_derivative NH P 0 T' ->
  has_normed_curve_derivative NX (fun t => ((x + t *: v, P t) : XP)) 0 (v, T').
Proof.
move=> hP e he; have [d0 [hd0 hd]] := hP e he; exists d0; split=> // h hh.
have hh0 : h != 0 by have /andP [hp _] := hh; rewrite -normr_gt0.
have e1 : h^-1 *: (x + (0 + h) *: v - (x + 0 *: v)) - v = 0.
  by rewrite add0r scale0r addr0 [x + _]addrC addrK scalerA mulVf // scale1r subrr.
have e2 : h^-1 *: (((x + (0 + h) *: v, P (0 + h)) : XP) - (x + 0 *: v, P 0)) - (v, T') =
    inj2 (h^-1 *: (P (0 + h) - P 0) - T').
  change ((h^-1 *: (x + (0 + h) *: v - (x + 0 *: v)) - v, h^-1 *: (P (0 + h) - P 0) - T') =
    (0, h^-1 *: (P (0 + h) - P 0) - T')).
  by rewrite e1.
change (NX (h^-1 *: (((x + (0 + h) *: v, P (0 + h)) : XP) - (x + 0 *: v, P 0)) - (v, T')) < e).
rewrite e2 product_second_injection_norm; exact: hd.
Qed.

(** Source for [ddg_point_flow_integrand]: Allard 3.2(1), p. 430,
    applied to the function (x, S) ↦ F(x, S) and to φ_t: the integrand
    F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ of F(φ_t# V) with respect
    to V. Definition. *)
Definition ddg_point_flow_integrand (t : R) (z : GB) : R :=
  F ((ddg_flow g t z.1,
    set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn) : XP) *
  image_bundle_jacobian (ddg_flow_differential Dg t) z.

(** Source for [ddg_point_first_variation_integrand]: DDG (A.8), p. 1144:
    the integrand D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x) of the first
    variation, with D_x F(x, S)(v) = DF(x, S)(v, 0) and B_F(x, S) the
    matrix of def:BF for the frozen integrand F(x, ·). Definition. *)
Definition ddg_point_first_variation_integrand (z : GB) : R :=
  DF ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)) ((g z.1 : Rn), (0 : Hom Rn Rn)) +
  HI (ddg_B d (fun S => F ((z.1 : Rn), S)) (set_val z.2 : Hom Rn Rn)) (Dg z.1).

(** Source for [ddg_point_flow_plane]: Allard 3.2, p. 430, and blueprint
    new:projection_formula: for |t| K < 1 the second component of
    (φ_t)_♮(x, S) is the orthogonal projection onto (1 + t Dg(x))[im S].
    Supporting lemma. *)
Lemma ddg_point_flow_plane (t : R) (z : GB) :
  `|t| * K < 1 ->
  is_ddg_plane_projection d (idn + t *: Dg z.1) (set_val z.2 : Hom Rn Rn)
    (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn).
Proof.
move=> htK; split; first exact: projection_grassmannP.
move=> y.
exact: (image_bundle_map_plane (ddg_flow g t) z y
  (fun x => ddg_flow_differential_injective (x := x) hg hK htK)).
Qed.

(** Source for [ddg_point_flow_integrand_zero]: φ_0 = 1_{R^n}, so the
    integrand at t = 0 is F(x, S). Supporting lemma. *)
Lemma ddg_point_flow_integrand_zero (z : GB) :
  ddg_point_flow_integrand 0 z = F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)).
Proof.
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have h0 : `|0 : R| * K < 1 by rewrite normr0 mul0r ltr01.
have hP := ddg_point_flow_plane z h0.
rewrite /ddg_point_flow_integrand (ddg_plane_zero hT hP) /ddg_flow scale0r addr0.
have -> : image_bundle_jacobian (ddg_flow_differential Dg 0) z = 1.
  rewrite /image_bundle_jacobian /ddg_flow_differential scale0r addr0.
  have -> : hom_comp idn (set_val z.2 : Hom Rn Rn) = set_val z.2.
    by apply: hom_ext=> x; rewrite hom_compE ddg_hom_idE.
  exact: ddg_jacobian_projection hT.
by rewrite mulr1.
Qed.

(** Source for [ddg_point_flow_integrand_derivative]: DDG (A.8), p. 1144:
    d/dt F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ at t = 0 equals
    D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x). Supporting lemma. *)
Lemma ddg_point_flow_integrand_derivative (z : GB) :
  has_real_curve_derivative (fun t => ddg_point_flow_integrand t z) 0
    (ddg_point_first_variation_integrand z).
Proof.
pose x : Rn := z.1.
pose T : Hom Rn Rn := set_val z.2.
pose L := Dg x.
pose P t := (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn).
pose J t := euclidean_linear_jacobian d (hom_comp (idn + t *: L) T).
pose T' := ddg_tangent_direction T L.
have hT : G T := projection_grassmannP z.2.
have hPd : exists2 delta : R, 0 < delta &
    forall t, `|t| < delta -> is_ddg_plane_projection d (idn + t *: L) T (P t).
  have hK1 : 0 < K + 1 by have := hK0; lra.
  exists (1 / (K + 1)); first by rewrite divr_gt0.
  move=> t ht; apply: ddg_point_flow_plane.
  have h1 : `|t| * (K + 1) < 1 / (K + 1) * (K + 1) by rewrite ltr_pM2r.
  rewrite divfK ?lt0r_neq0 // in h1.
  have h2 := normr_ge0 t; nra.
have hP' : has_normed_curve_derivative NH P 0 T' := ddg_lemma_A_1 hT hPd.
have hP0 : P 0 = T.
  have [delta hdelta hPt] := hPd.
  by apply: (ddg_plane_zero (L := L) hT); apply: hPt; rewrite normr0.
have hB := ddg_B_spec hT (ddg_frozen_differentiable x hT).
have hA6 := ddg_weighted_jacobian_derivative hT hB hPd.
have hD := norm_class_one_differential hF (hU x hT).
have hc10 : ((x + 0 *: g x, P 0) : XP) = (x, T) by rewrite scale0r addr0 hP0.
have hc20 : ((x + 0 *: 0, P 0) : XP) = (x, T) by rewrite scale0r addr0 hP0.
have [hd1 _] := ddg_curve_chain (P := fun t => ((x + t *: g x, P t) : XP)) hNX hc10
  (ddg_pair_curve_derivative x (g x) hP') hD.
have [hd2 _] := ddg_curve_chain (P := fun t => ((x + t *: 0, P t) : XP)) hNX hc20
  (ddg_pair_curve_derivative x 0 hP') hD.
have hsub := has_real_curve_derivative_subtract hd1 hd2.
have hJ := ddg_jacobian_derivative L hT.
have hprod := real_curve_derivative_product hsub hJ.
have hsum := ddg_real_curve_derivative_add hprod hA6.
have e1 : (fun t => ddg_point_flow_integrand t z) =
    (fun t => (F (x + t *: g x, P t) - F (x + t *: 0, P t)) * J t + F (x, P t) * J t).
  apply: funext=> t; rewrite scaler0 addr0.
  change (F (x + t *: g x, P t) * J t = (F (x + t *: g x, P t) - F (x, P t)) * J t + F (x, P t) * J t).
  ring.
have hJ0 : J 0 = 1.
  rewrite /J scale0r addr0.
  have -> : hom_comp idn T = T by apply: hom_ext=> y; rewrite hom_compE ddg_hom_idE.
  exact: ddg_jacobian_projection hT.
have e3 : DF (x, T) (g x, 0) = DF (x, T) (g x, T') - DF (x, T) (0, T').
  have -> : ((g x, 0) : XP) = (g x, T') - (0, T').
    by change ((g x, 0) = (g x - 0, T' - T')); rewrite subr0 subrr.
  by rewrite linearB.
have e2 : ddg_point_first_variation_integrand z =
    (DF (x, T) (g x, T') - DF (x, T) (0, T')) * J 0 +
      (F (x + 0 *: g x, P 0) - F (x + 0 *: 0, P 0)) * HI L T +
    HI (ddg_B d (fun S => F (x, S)) T) L.
  by rewrite hJ0 hc10 hc20 subrr mul0r addr0 mulr1 -e3.
rewrite e1 e2; exact: hsum.
Qed.

(** Source for [ddg_point_flow_integrand_outside]: blueprint new:flow:
    if |x| ≥ ρ, then g(x) = 0 and Dg(x) = 0, so φ_t(x) = x,
    Dφ_t(x) = 1_{R^n}, and the integrand does not depend on t.
    Supporting lemma. *)
Lemma ddg_point_flow_integrand_outside (t : R) (z : GB) :
  `|t| * K < 1 -> rho <= Nn z.1 -> ddg_point_flow_integrand t z = ddg_point_flow_integrand 0 z.
Proof.
move=> htK hz; have [hg0 hDg0] := hsupp hz.
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have hP := ddg_point_flow_plane z htK.
have e : idn + t *: Dg z.1 = idn + 0 *: (0 : Hom Rn Rn) by rewrite hDg0 !scaler0.
rewrite e in hP; have hP0 := ddg_plane_zero hT hP.
rewrite ddg_point_flow_integrand_zero /ddg_point_flow_integrand hP0 /ddg_flow hg0 scaler0 addr0.
have -> : image_bundle_jacobian (ddg_flow_differential Dg t) z = 1.
  rewrite /image_bundle_jacobian /ddg_flow_differential hDg0 scaler0 addr0.
  have -> : hom_comp idn (set_val z.2 : Hom Rn Rn) = set_val z.2.
    by apply: hom_ext=> y; rewrite hom_compE ddg_hom_idE.
  exact: ddg_jacobian_projection hT.
by rewrite mulr1.
Qed.

(** Source for [ddg_point_compact]: the set
    {(x, S) : |x| ≤ r, S ∈ G(n, d)} is compact in R^n × Hom(R^n, R^n), as
    the product of a closed ball and the compact set G(n, d) (Allard 2.3),
    by the compactness of products of two compact spaces and the continuity
    of the identity map onto the product inner metric of Federer 1.7.11,
    p. 36. Supporting lemma. *)
Lemma ddg_point_compact (r : R) :
  @compact (real_norm_metric_space hNX) [set p : XP | Nn p.1 <= r /\ G p.2].
Proof.
have hb := @euclidean_closed_metric_ball_compact R n 0 r.
have hG := @orthogonal_projectors_compact R n d.
have hP := compact_setX hb hG.
have hc : continuous (fun s : (inner_metric_space hBn * inner_metric_space hHI)%type =>
    ((s.1, s.2) : inner_metric_space hX)).
  exact: (inner_cartesian_pair_continuous (@first_projection_continuous _ _)
    (@second_projection_continuous _ _)).
have hi := continuous_compact (continuous_subspaceT hc) hP.
apply: (inner_norm_compact_topology_iff hX _).1.
suff -> : [set p : XP | Nn p.1 <= r /\ G p.2] =
    (fun s : (inner_metric_space hBn * inner_metric_space hHI)%type =>
      ((s.1, s.2) : inner_metric_space hX)) @` (metric_closed_ball (0 : inner_metric_space hBn) r `*` G) by [].
apply/seteqP; split.
- move=> [x S] [hx hS]; exists (x, S)=> //; split=> //=.
  by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
- move=> p [[x S] [hx hS] <-]; split=> //=.
  by move: hx; rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
Qed.

(** Source for [ddg_point_integrand_continuous]: Allard 3.2, p. 430: for
    |t| K < 1 the integrand F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ is
    continuous on G_d(R^n), since F is continuous on U (Federer 3.1.1,
    p. 210) and (φ_t)_♮ is continuous. Supporting lemma. *)
Lemma ddg_point_integrand_continuous (t : R) :
  `|t| * K < 1 -> continuous (fun z : GB => (ddg_point_flow_integrand t z : real_line_metric R)).
Proof.
move=> htK z.
have hinj x : injective (ddg_flow_differential Dg t x).
  exact: (ddg_flow_differential_injective hg hK htK).
have h1 := @image_bundle_map_continuous R n d _ _ (ddg_flow_class_one hg t) hinj.
have hx : continuous (fun z : GB => (ddg_flow g t z.1 : inner_metric_space hBn)).
  exact: (continuous_function_composition (@grassmann_bundle_point_continuous R n d)
    (class_one_continuous (ddg_flow_class_one hg t))).
have hS : continuous (fun z : GB =>
    (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2
      : inner_metric_space hHI)).
  have h2 : continuous (fun z : GB => (set_val z.2 : inner_metric_space hHI)).
    apply: (continuous_function_composition (@grassmann_bundle_plane_continuous R n d)).
    exact: metric_subset_inclusion_continuous.
  exact: (continuous_function_composition h1 h2).
have hp := inner_cartesian_pair_continuous hx hS.
have hi := homeomorphism_continuous (inner_own_norm_homeomorphism hX).
have hpU : U ((ddg_flow g t z.1,
    set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn) : XP).
  exact: hU (projection_grassmannP _).
have hFc := norm_class_zero_continuous_at hNX (hNY := hN1) (norm_class_one_zero hF) hpU.
have hk : continuous (fun s : real_norm_metric_space hN1 => (s : real_line_metric R)).
  apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=> a b.
  by rewrite real_line_metric_distanceE real_norm_metric_distanceE mul1r.
have hFp := continuous_comp (hp z) (continuous_comp (hi _) (continuous_comp hFc (hk _))).
have hJ := @image_bundle_jacobian_continuous R n d _ _ (ddg_flow_class_one hg t).
exact: (@continuousM R GB _ _ z hFp (hJ z)).
Qed.

(** Source for [ddg_point_integrand_difference_borel]: for |t| K < 1 the
    difference of the integrands at t and at 0 is continuous, hence a Borel
    function, Federer 2.2.14, p. 70. Supporting lemma. *)
Lemma ddg_point_integrand_difference_borel (t : R) :
  `|t| * K < 1 ->
  is_borel_function ((fun z : GB => ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z)
    : GB -> real_line_metric R).
Proof.
move=> htK.
have h0 : `|0 : R| * K < 1 by rewrite normr0 mul0r ltr01.
have hf : continuous (fun z : GB => (ddg_point_flow_integrand t z : R^o)) :=
  ddg_point_integrand_continuous htK.
have hf0 : continuous (fun z : GB => (ddg_point_flow_integrand 0 z : R^o)) :=
  ddg_point_integrand_continuous h0.
have hpair := topological_pair_continuous hf hf0.
have hc : continuous (fun z : GB =>
    (ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z : R^o)).
  move=> z; exact: (continuous_comp (hpair z) (@sub_continuous R^o _)).
have hc' : continuous (fun z : GB =>
    (ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z : real_line_metric R)) := hc.
exact: continuous_borel_function hc'.
Qed.

(** Source for [ddg_point_ball_summable]: Federer 2.4.4, p. 82, and
    2.2.5, p. 61: the characteristic function of
    {(x, S) : |x| < ρ} is V summable, since this set is open and contained
    in the compact set {(x, S) : |x| ≤ ρ} (Allard 3.1), and V is a Radon
    measure. Supporting lemma. *)
Lemma ddg_point_ball_summable :
  exists a : R, is_measure_integral V
    (real_total_integrand (fun z : GB => if Nn z.1 < rho then 1 else 0)) a%:E.
Proof.
have [hm hr] := hV.
pose A := [set z : GB | Nn z.1 < rho].
have hAo : open A.
  have -> : A = @grassmann_bundle_point R n d @^-1` [set y : inner_metric_space hBn | mdist (0 : inner_metric_space hBn) y < rho].
    apply/seteqP; split=> z /=; rewrite /grassmann_bundle_point inner_metric_distanceE sub0r
      inner_normN; exact.
  exact: (continuousP _).1 (@grassmann_bundle_point_continuous R n d) _ (metric_open_ball_open _ _).
have hAm := radon_open_measurable hr hAo.
have hc : is_characteristic_function A
    (fun z : GB => (if Nn z.1 < rho then 1 else 0 : real_line_metric R)).
  split=> z hz.
  - by rewrite ifT.
  - by rewrite ifF //; apply/negbTE/negP.
have hi := measure_characteristic_integral hm hc hAm.
have hfin : (V A < +oo)%E.
  have hB := @grassmann_bundle_point_proper R n d _ (@euclidean_closed_metric_ball_compact R n 0 rho).
  apply: (le_lt_trans _ (radon_compact_finite hr hB)); apply: (measure_mono hm)=> z hz.
  rewrite /metric_closed_ball /= /grassmann_bundle_point inner_metric_distanceE sub0r inner_normN.
  exact: ltW.
have hfn : V A \is a fin_num by rewrite ge0_fin_numE // (measure_nonnegative hm A).
by rewrite -(fineK hfn) in hi; exists (fine (V A)).
Qed.

(** Source for [ddg_point_flow_integrand_estimate]: proof of DDG Lemma
    A.2, p. 1144: if |x| < ρ, |t| ≤ 1, |t| K < 1 and |t| n^{1/2} K ≤ 1/2,
    and if F is Lipschitzian with constant Λ and bounded by Φ on
    {(y, S) : |y| ≤ ρ + M, S ∈ G(n, d)}, then the integrand at t differs
    from F(x, S) by at most 2^d (Λ (M + 3 n K) + Φ n^{1/2} K) |t|.
    Supporting lemma. *)
Lemma ddg_point_flow_integrand_estimate (Lam Phi t : R) (z : GB) :
  0 <= Lam ->
  (forall p q : XP, Nn p.1 <= rho + M -> G p.2 -> Nn q.1 <= rho + M -> G q.2 ->
    `|F p - F q| <= Lam * NX (p - q)) ->
  (forall p : XP, Nn p.1 <= rho + M -> G p.2 -> `|F p| <= Phi) ->
  `|t| <= 1 -> `|t| * K < 1 -> `|t| * (Num.sqrt n%:R * K) <= 1 / 2 -> Nn z.1 < rho ->
  `|ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z| <=
    2 ^+ d * (Lam * (M + 3 * (Num.sqrt n%:R * (Num.sqrt n%:R * K))) + Phi * (Num.sqrt n%:R * K)) *
      `|t|.
Proof.
move=> hLam hFL hFb ht1 htK hts hz.
rewrite ddg_point_flow_integrand_zero.
pose P := (set_val (image_bundle_map (ddg_flow g t) (ddg_flow_differential Dg t) z).2 : Hom Rn Rn).
pose J := euclidean_linear_jacobian d (hom_comp (idn + t *: Dg z.1) (set_val z.2 : Hom Rn Rn)).
change (`|F ((z.1 + t *: g z.1, P) : XP) * J - F ((z.1, set_val z.2) : XP)| <=
  2 ^+ d * (Lam * (M + 3 * (Num.sqrt n%:R * (Num.sqrt n%:R * K))) + Phi * (Num.sqrt n%:R * K)) *
    `|t|).
have hT : G (set_val z.2 : Hom Rn Rn) := projection_grassmannP z.2.
have hP : is_ddg_plane_projection d (idn + t *: Dg z.1) (set_val z.2 : Hom Rn Rn) P :=
  ddg_point_flow_plane z htK.
have [hGP _] := hP.
have hsn : 0 <= Num.sqrt n%:R :> R := sqrtr_ge0 _.
have hLb : NH (Dg z.1) <= Num.sqrt n%:R * K.
  apply: ddg_hom_norm_from_vector_bound=> // v.
  exact: (ddg_flow_differential_bound hg z.1 v hK).
have hL0 : 0 <= NH (Dg z.1) := ddg_hom_norm_nonnegative (Dg z.1).
have ht0 := normr_ge0 t.
have h4 : `|t| * NH (Dg z.1) <= `|t| * (Num.sqrt n%:R * K) := ler_wpM2l ht0 hLb.
have hs : NH (Dg z.1) * `|t| <= 1 / 2 by rewrite mulrC; exact: le_trans h4 hts.
have hJb : J <= 2 ^+ d := ddg_jacobian_bound hT hs.
have hc1 : `|t| * NH (Dg z.1) < 1 by rewrite mulrC; lra.
have hJ0 : 0 <= J.
  apply: (le_trans _ (ddg_jacobian_lower hT hc1)); apply: exprn_ge0; lra.
have hJe : `|J - 1| <= 2 ^+ d * (`|t| * NH (Dg z.1)) := ddg_jacobian_estimate hT hs.
have hPT : NH (P - set_val z.2) <= Num.sqrt n%:R * (3 * (`|t| * NH (Dg z.1))) :=
  ddg_plane_hom_estimate hT hP hs.
have hM0 : 0 <= M by apply: le_trans (hM z.1); exact: inner_norm_nonnegative.
have hgx : Nn (t *: g z.1) <= `|t| * M.
  by rewrite inner_normZ; apply: ler_wpM2l; [exact: normr_ge0 | exact: hM].
have htM : `|t| * M <= M by rewrite -[X in _ <= X]mul1r ler_wpM2r.
have hq1 : Nn (z.1 + t *: g z.1) <= rho + M.
  have h1 := inner_norm_triangle hBn z.1 (t *: g z.1); have h2 := ltW hz; lra.
have hq0 : Nn z.1 <= rho + M by have := ltW hz; lra.
have hd := hFL ((z.1 + t *: g z.1, P) : XP) ((z.1, set_val z.2) : XP) hq1 hGP hq0 hT.
have hdn : NX (((z.1 + t *: g z.1, P) : XP) - (z.1, set_val z.2)) <=
    `|t| * M + Num.sqrt n%:R * (3 * (`|t| * NH (Dg z.1))).
  have -> : ((z.1 + t *: g z.1, P) : XP) - (z.1, set_val z.2) = (t *: g z.1, P - set_val z.2).
    change ((z.1 + t *: g z.1 - z.1, P - set_val z.2) = (t *: g z.1, P - set_val z.2)).
    by rewrite [z.1 + _]addrC addrK.
  apply: (le_trans (ddg_pair_norm _ _)); lra.
have e : F ((z.1 + t *: g z.1, P) : XP) * J - F ((z.1, set_val z.2) : XP) =
    (F (z.1 + t *: g z.1, P) - F (z.1, set_val z.2)) * J + F (z.1, set_val z.2) * (J - 1).
  by ring.
rewrite e; apply: (le_trans (ler_normD _ _)); rewrite !normrM (ger0_norm hJ0).
have ha : `|F (z.1 + t *: g z.1, P) - F (z.1, set_val z.2)| <=
    Lam * (`|t| * M + Num.sqrt n%:R * (3 * (`|t| * NH (Dg z.1)))) :=
  le_trans hd (ler_wpM2l hLam hdn).
have hb : `|F (z.1, set_val z.2)| <= Phi := hFb ((z.1, set_val z.2) : XP) hq0 hT.
have hPhi0 : 0 <= Phi := le_trans (normr_ge0 _) hb.
have h2d : 0 <= 2 ^+ d :> R by rewrite exprn_ge0.
have h1 := ler_pM (normr_ge0 _) hJ0 ha hJb.
have h2 := ler_pM (normr_ge0 _) (normr_ge0 _) hb hJe.
have h3 : Num.sqrt n%:R * (3 * (`|t| * NH (Dg z.1))) <=
    Num.sqrt n%:R * (3 * (`|t| * (Num.sqrt n%:R * K))).
  apply: ler_wpM2l=> //; apply: ler_wpM2l; [lra | exact: h4].
have h5 : Lam * (`|t| * M + Num.sqrt n%:R * (3 * (`|t| * NH (Dg z.1)))) * 2 ^+ d <=
    Lam * (`|t| * M + Num.sqrt n%:R * (3 * (`|t| * (Num.sqrt n%:R * K)))) * 2 ^+ d.
  by apply: ler_wpM2r=> //; apply: ler_wpM2l=> //; rewrite lerD2l.
have h6 : Phi * (2 ^+ d * (`|t| * NH (Dg z.1))) <= Phi * (2 ^+ d * (`|t| * (Num.sqrt n%:R * K))).
  by apply: ler_wpM2l=> //; apply: ler_wpM2l.
have e2 : 2 ^+ d * (Lam * (M + 3 * (Num.sqrt n%:R * (Num.sqrt n%:R * K))) +
    Phi * (Num.sqrt n%:R * K)) * `|t| =
    Lam * (`|t| * M + Num.sqrt n%:R * (3 * (`|t| * (Num.sqrt n%:R * K)))) * 2 ^+ d +
    Phi * (2 ^+ d * (`|t| * (Num.sqrt n%:R * K))) by ring.
rewrite e2; apply: (le_trans (lerD h1 h2)); exact: lerD h5 h6.
Qed.

(** Source for [ddg_lemma_A_2_delta]: DDG Lemma A.2, (A.8), p. 1144, with
    the additional information that |t| K < 1 for |t| < δ. Supporting
    lemma for [ddg_lemma_A_2] and [ddg_lemma_A_2_image]. *)
Lemma ddg_lemma_A_2_delta :
  exists delta c : R, [/\ 0 < delta, forall t : R, `|t| < delta -> `|t| * K < 1,
    is_measure_integral V (real_total_integrand ddg_point_first_variation_integrand) c%:E,
    forall t, `|t| < delta -> exists a : R, is_measure_integral V
      (real_total_integrand (fun z : GB =>
        ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta -> is_measure_integral V
        (real_total_integrand (fun z : GB =>
          ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
have hm := varifold_measure hV.
pose sK := Num.sqrt n%:R * K.
have hsK : 0 <= sK by rewrite mulr_ge0 // sqrtr_ge0.
pose s := sK + K + 1.
have hs : 0 < s by rewrite /s; have := hK0; lra.
pose delta := 1 / (2 * s).
have hdelta : 0 < delta by rewrite /delta divr_gt0 // mulr_gt0.
have hdt (t : R) : `|t| < delta -> [/\ `|t| <= 1, `|t| * K < 1 & `|t| * sK <= 1 / 2].
  move=> ht.
  have h2s : 0 < 2 * s by rewrite mulr_gt0.
  have h1 : `|t| * (2 * s) < delta * (2 * s) by rewrite ltr_pM2r.
  rewrite /delta divfK ?lt0r_neq0 // in h1.
  have h2 := normr_ge0 t.
  have h3 : 0 <= `|t| * sK by rewrite mulr_ge0.
  have h4 : 0 <= `|t| * K by rewrite mulr_ge0.
  rewrite /s in h1; split; nra.
have hQU : [set p : XP | Nn p.1 <= rho + M /\ G p.2] `<=` U.
  by move=> [x S] [_ hS]; exact: hU hS.
have hQc := ddg_point_compact (r := rho + M).
have [Lam [hLam [_ hLip]]] := norm_class_one_compact_lipschitz hN1 (ex_intro _ DF hF) hQU hQc.
have hFL (p q : XP) : Nn p.1 <= rho + M -> G p.2 -> Nn q.1 <= rho + M -> G q.2 ->
    `|F p - F q| <= Lam * NX (p - q).
  move=> hp1 hp2 hq1 hq2; have := hLip p q (conj hp1 hp2) (conj hq1 hq2).
  by rewrite !real_norm_metric_distanceE.
have [Phi [_ hPhi]] := norm_class_zero_compact_bounded hN1 hQc hQU (norm_class_one_zero hF).
have hFb (p : XP) : Nn p.1 <= rho + M -> G p.2 -> `|F p| <= Phi.
  by move=> hp1 hp2; exact: hPhi p (conj hp1 hp2).
pose C := 2 ^+ d * (Lam * (M + 3 * (Num.sqrt n%:R * sK)) + Phi * sK).
pose w (z : GB) := C * (if Nn z.1 < rho then 1 else 0).
have hw : is_measure_summable V (real_total_integrand w).
  have [a ha] := ddg_point_ball_summable.
  by exists (C * a); exact: (real_total_integral_scale hm C ha).
have hdom (t : R) (z : GB) : `|t| < delta ->
    `|ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z| <= `|t| * w z.
  move=> ht; have [ht1 htK hts] := hdt t ht.
  rewrite /w; case: ifP=> hz.
  - have h := ddg_point_flow_integrand_estimate (ltW hLam) hFL hFb ht1 htK hts hz.
    apply: (le_trans h); rewrite mulr1 mulrC /C /sK; exact: lexx.
  - have hz' : rho <= Nn z.1 by rewrite leNgt hz.
    by rewrite (ddg_point_flow_integrand_outside htK hz') subrr normr0 !mulr0.
have hmeas (t : R) : `|t| < delta -> is_measure_measurable_function V
    (real_total_integrand (fun z => ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z)).
  move=> ht; have [_ htK _] := hdt t ht.
  exact: (varifold_borel_measurable hV (ddg_point_integrand_difference_borel htK)).
have [c [hc hint hder]] := ddg_integral_derivative hm hdelta hw hmeas hdom
  ddg_point_flow_integrand_derivative.
have e (t : R) : (fun z : GB => ddg_point_flow_integrand t z - ddg_point_flow_integrand 0 z) =
    (fun z : GB => ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn))).
  by apply: funext=> z; rewrite ddg_point_flow_integrand_zero.
exists delta, c; split=> //.
- by move=> t ht; have [_ h _] := hdt t ht.
- by move=> t ht; have [a ha] := hint t ht; exists a; rewrite -e.
- by move=> I hI; apply: hder=> t ht; rewrite e; exact: hI.
Qed.

(** Source for [ddg_lemma_A_2]: DDG Lemma A.2, (A.8), p. 1144; blueprint
    ddg:A.2: for some δ > 0, (x, S) ↦ D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x)
    is V summable with integral c, the function
    (x, S) ↦ F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ - F(x, S) is V
    summable for |t| < δ, and its integral, as a function of t, has
    derivative c at 0. By Allard 3.2(1) the integral of this difference is
    F(φ_t# V) - F(V) whenever F(V) is finite ([ddg_lemma_A_2_image]).
    Direct formalisation, with the hypotheses stated in the module
    header. *)
Theorem ddg_lemma_A_2 :
  exists delta c : R, [/\ 0 < delta,
    is_measure_integral V (real_total_integrand ddg_point_first_variation_integrand) c%:E,
    forall t, `|t| < delta -> exists a : R, is_measure_integral V
      (real_total_integrand (fun z : GB =>
        ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta -> is_measure_integral V
        (real_total_integrand (fun z : GB =>
          ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
have [delta [c [hdelta _ hc hint hder]]] := ddg_lemma_A_2_delta.
by exists delta, c; split.
Qed.

(** Source for [ddg_lemma_A_2_image]: DDG Lemma A.2, (A.8), p. 1144, in
    terms of the image varifolds φ_t# V of Allard 3.2, p. 430: if
    F(V) = ∫ F(x, S) dV(x, S) is finite, then for some δ > 0 the energy
    F(φ_t# V) is finite for |t| < δ, and d/dt F(φ_t# V) at t = 0 equals
    ∫ D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x) dV(x, S). Direct
    formalisation. *)
Theorem ddg_lemma_A_2_image (a0 : R) :
  is_measure_integral V
    (real_total_integrand (fun z : GB => F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) a0%:E ->
  exists delta c : R, [/\ 0 < delta,
    is_measure_integral V (real_total_integrand ddg_point_first_variation_integrand) c%:E,
    forall t, `|t| < delta -> exists a : R,
      is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
        (real_total_integrand (fun z : GB => F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) a%:E &
    forall I : R -> R,
      (forall t, `|t| < delta ->
        is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
          (real_total_integrand (fun z : GB => F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn))))
          (I t)%:E) ->
      has_real_curve_derivative I 0 c].
Proof.
move=> h0.
have hm := varifold_measure hV.
have [delta [c [hdelta htK hc hint hder]]] := ddg_lemma_A_2_delta.
have halpha : is_borel_function
    ((fun z : GB => F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn))) : GB -> real_line_metric R).
  have h00 : `|0 : R| * K < 1 by rewrite normr0 mul0r ltr01.
  have hc0 := ddg_point_integrand_continuous h00.
  have e : (fun z : GB => (ddg_point_flow_integrand 0 z : real_line_metric R)) =
      (fun z : GB => F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn))).
    by apply: funext=> z; exact: ddg_point_flow_integrand_zero.
  rewrite e in hc0; exact: continuous_borel_function hc0.
have himm (t : R) : `|t| < delta ->
    is_proper_class_one_immersion (ddg_flow g t) (ddg_flow_differential Dg t).
  by move=> ht; exact: (ddg_flow_immersion hg hK hK0 hM (htK t ht)).
have hsplit (t a : R) : is_measure_integral V (real_total_integrand (fun z : GB =>
      ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) a%:E ->
    is_measure_integral V (real_total_integrand (ddg_point_flow_integrand t)) (a + a0)%:E.
  move=> ha; have h := real_total_integral_add hm ha h0.
  have e : (fun z : GB => ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)) +
      F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn))) = ddg_point_flow_integrand t.
    by apply: funext=> z; rewrite subrK.
  by rewrite e in h.
exists delta, c; split=> //.
- move=> t ht; have [a ha] := hint t ht.
  exists (a + a0); apply/(allard_3_2_1_integral hV (himm t ht) halpha _).
  exact: hsplit ha.
- move=> I hI.
  have hI' (t : R) : `|t| < delta -> is_measure_integral V (real_total_integrand (fun z : GB =>
      ddg_point_flow_integrand t z - F ((z.1 : Rn), (set_val z.2 : Hom Rn Rn)))) (I t - a0)%:E.
    move=> ht.
    have h := (allard_3_2_1_integral hV (himm t ht) halpha _).1 (hI t ht).
    exact: (real_total_integral_subtract hm h h0).
  have hd := hder (fun t => I t - a0) hI'.
  move: hd; rewrite /has_real_curve_derivative; apply: punctured_real_limit_congr=> h _.
  by congr (_ * _); ring.
Qed.

End FirstVariationPoint.

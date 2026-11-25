(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:varifolds and lem:first_variation, after De Philippis, De Rosa and
    Ghiraldin (2018), Lemma A.2, for an integrand F not depending on the
    point.

    Let E be a realisation of the smooth maps R^n -> R^n (Federer 4.1.1)
    and D(R^n, R^n) its test space [smooth_test_space hE]. For
    g ∈ D(R^n, R^n), with differentials Dg(x) for x ∈ R^n, let
    φ_t(x) = x + t g(x) ([ddg_flow]). There is 0 < t_0 such that φ_t is
    injective and a proper immersion of class 1 for |t| < t_0
    ([dgpr_test_flow]); that φ_t maps R^n onto R^n is not formalised
    (docs/divergences.md). The image varifold φ_{t#} V is Allard's
    [image_varifold] (Allard 3.2). With F(W) = ∫ F(S) dW(x, S), the
    number δ_F V(g) = d/dt F(φ_{t#} V)|_{t=0} is characterised by the
    predicate [is_dgpr_first_variation V F g Dg c]: for some 0 < δ the
    integral F(φ_{t#} V) exists for |t| < δ, and every function I with
    I(t) = F(φ_{t#} V) for |t| < δ has the derivative c at 0 (Federer
    2.9.19). This number is unique ([dgpr_first_variation_unique]); no
    object is chosen.

    Theorem [dgpr_first_variation] is lem:first_variation: if V is a
    varifold with ‖V‖(R^n) < ∞ and F is of class 1 relative to G(n, k)
    (Federer 3.1.22), then δ_F V(g) exists and
        δ_F V(g) = ∫ B_F(S) • Dg(x) dV(x, S),
    with B_F of def:BF ([dgpr_B]). It is DDG Lemma A.2 for an integrand
    not depending on the point ([ddg_lemma_A_2_constant_lipschitz]); the
    Lipschitz bound and the bound of g required there follow from the
    compactness of the support of g ([dgpr_test_lipschitz],
    [dgpr_test_bounded]). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity RelativeClassUP
  NormCompactFunctionBound NormLocalLipschitzScalarProduct EuclideanLocalLipschitzCompactSupport
  LipschitzUP RealCurveDerivativeUP PartialFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation SmoothFunctionSupport.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds AllardImageVarifoldMaps AllardImageVarifoldUP AllardImageVarifold.
From DPDRG Require Import DdgAnisotropicIntegrand DdgFlow DdgFirstVariation.
From DPGPR Require Import DgprAnisotropicIntegrand.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TestFields.
Variable R : realType.
Variable n : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Variable E : lmodType R.
Variable ev : E -> Rn -> Rn.
Hypothesis hE : is_smooth_function_space hNn hNn setT ev.
Variable g : smooth_test_space hE.
Local Notation gv := (smooth_test_value hE g).

(** Source for [dgpr_test_class_one]: Federer 4.1.1, p. 344, and
    3.1.1, p. 210: every g ∈ D(R^n, R^n) is of class ∞; hence, if Dg(x)
    is the differential of g at x for x ∈ R^n, then g is of class 1 with
    the continuous differential Dg. Supporting lemma. *)
Lemma dgpr_test_class_one (Dg : Rn -> Hom Rn Rn) :
  (forall x, has_norm_differential Nn Nn setT gv x (Dg x)) ->
  is_norm_class_one_field Nn Nn setT gv Dg.
Proof.
move=> hD.
have [D0 hD0] := (norm_class_firstP hNn hNn setT gv).1 (smooth_test_value_smooth hE g 1%N).
have -> : Dg = D0.
  apply: funext => x.
  exact: (norm_differential_unique hNn hNn (hD x) (norm_class_one_differential hD0 (Logic.I : setT x))).
exact: hD0.
Qed.

(** Source for [dgpr_test_support_zero]: Federer 4.1.1, p. 344: g(x) = 0
    for x ∈ R^n ∖ spt g. Supporting lemma. *)
Lemma dgpr_test_support_zero (x : Rn) :
  ~ [set y : real_norm_metric_space hNn |
      @smooth_function_support R Rn Rn Nn hNn setT (smooth_test_space hE)
        (smooth_test_value hE) g y] x -> gv x = 0.
Proof.
move=> hx; apply: contrapT => hne; apply: hx; split=> //.
exact: subset_closure.
Qed.

(** Source for [dgpr_test_lipschitz]: blueprint lem:first_variation,
    hypothesis of DDG Lemma A.2: every g ∈ D(R^n, R^n) is Lipschitz,
    since g is of class 1 and spt g is compact (Federer 4.1.1, p. 345).
    Supporting lemma. *)
Lemma dgpr_test_lipschitz : exists2 K : R, 0 <= K & forall y z, Nn (gv y - gv z) <= K * Nn (y - z).
Proof.
have hC := smooth_test_support_compact hE g.
have hloc : @is_locally_metric_lipschitz R (real_norm_metric_space hNn) (real_norm_metric_space hNn)
    setT gv.
  apply: (@norm_class_one_locally_metric_lipschitz R _ _ _ _ hNn hNn setT gv).
  exact: (norm_class_firstP hNn hNn setT gv).1 (smooth_test_value_smooth hE g 1%N).
have [L [hL hLb]] := euclidean_local_lipschitz_compact_support_global hC
  dgpr_test_support_zero hloc.
by exists L => //; exact: ltW.
Qed.

(** Source for [dgpr_test_bounded]: blueprint lem:first_variation,
    hypothesis of DDG Lemma A.2: every g ∈ D(R^n, R^n) is bounded, since g
    is continuous and spt g is compact (Federer 4.1.1, p. 345).
    Supporting lemma. *)
Lemma dgpr_test_bounded : exists M : R, forall y, Nn (gv y) <= M.
Proof.
have hC := smooth_test_support_compact hE g.
have [D0 hD0] := (norm_class_firstP hNn hNn setT gv).1 (smooth_test_value_smooth hE g 1%N).
have [M [hM hMb]] := @norm_class_zero_compact_bounded R _ _ _ _ hNn hNn setT _ gv hC
  (@subsetT _ _) (norm_class_one_zero hD0).
exists M => y.
have [hy|hy] := pselect ([set y : real_norm_metric_space hNn |
    @smooth_function_support R Rn Rn Nn hNn setT (smooth_test_space hE)
      (smooth_test_value hE) g y] y).
- exact: hMb.
- by rewrite (dgpr_test_support_zero hy) (inner_norm0 hBn) ltW.
Qed.

End TestFields.

Section FirstVariation.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [is_dgpr_first_variation]: blueprint mr:varifolds and
    lem:first_variation: c = δ_F V(g) = d/dt F(φ_{t#} V)|_{t=0}, where
    F(W) = ∫ F(S) dW(x, S) (DPGPR 2026, (1.3)) and φ_t = [ddg_flow g t].
    The predicate asserts that for some 0 < δ the integral F(φ_{t#} V)
    exists for |t| < δ, and that every function I with
    I(t) = F(φ_{t#} V) for |t| < δ has the derivative c at 0 (Federer
    2.9.19, p. 163). Definition. *)
Definition is_dgpr_first_variation (V : set GB -> \bar R) (F : Hom Rn Rn -> R)
    (g : Rn -> Rn) (Dg : Rn -> Hom Rn Rn) (c : R) : Prop :=
  exists2 delta : R, 0 < delta &
    (forall t, `|t| < delta -> exists a : R,
      is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
        (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) a%:E) /\
    forall I : R -> R,
      (forall t, `|t| < delta ->
        is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
          (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) (I t)%:E) ->
      has_real_curve_derivative I 0 c.

(** Source for [dgpr_first_variation_unique]: uniqueness of the
    derivative (Federer 2.9.19, p. 163): the number δ_F V(g) of
    [is_dgpr_first_variation] is unique. Supporting lemma. *)
Lemma dgpr_first_variation_unique V F g Dg c c' :
  is_dgpr_first_variation V F g Dg c -> is_dgpr_first_variation V F g Dg c' -> c = c'.
Proof.
move=> [d1 hd1 [he1 hD1]] [d2 hd2 [he2 hD2]].
pose P t a := is_measure_integral (image_varifold (ddg_flow g t) (ddg_flow_differential Dg t) V)
  (real_total_integrand (fun z : GB => F (set_val z.2 : Hom Rn Rn))) a%:E.
pose I t : R := if pselect (exists a, P t a) is left h then projT1 (cid h) else 0.
have hI t : (exists a, P t a) -> P t (I t).
  move=> h; rewrite /I; case: pselect => [h'|//]; exact: projT2 (cid h').
have h1 := hD1 I (fun t ht => hI t (he1 t ht)).
have h2 := hD2 I (fun t ht => hI t (he2 t ht)).
exact: punctured_real_limit_unique h1 h2.
Qed.

Variable E : lmodType R.
Variable ev : E -> Rn -> Rn.
Hypothesis hE : is_smooth_function_space hNn hNn setT ev.

(** Source for [dgpr_test_flow]: blueprint lem:first_variation, first
    assertion, as stated in the proof of DDG Lemma A.2: there is
    0 < t_0 such that φ_t is injective and a proper immersion of class 1
    of R^n for |t| < t_0. That φ_t maps R^n onto R^n is not asserted
    (docs/divergences.md). Direct formalisation. *)
Theorem dgpr_test_flow (g : smooth_test_space hE) (Dg : Rn -> Hom Rn Rn) :
  (forall x, has_norm_differential Nn Nn setT (smooth_test_value hE g) x (Dg x)) ->
  exists2 t0 : R, 0 < t0 & forall t, `|t| < t0 ->
    injective (ddg_flow (smooth_test_value hE g) t) /\
    is_proper_class_one_immersion (ddg_flow (smooth_test_value hE g) t) (ddg_flow_differential Dg t).
Proof.
move=> hD.
have hg := dgpr_test_class_one hD.
have [K hK0 hK] := dgpr_test_lipschitz g.
have [M hM] := dgpr_test_bounded g.
have hK1 : 0 < K + 1 by rewrite ltr_wpDl.
exists (K + 1)^-1; first by rewrite invr_gt0.
move=> t ht.
have htK : `|t| * K < 1.
  have h0 := normr_ge0 t.
  have h1 : `|t| * (K + 1) < 1 by rewrite -ltr_pdivlMr // div1r.
  have h2 : `|t| * K <= `|t| * (K + 1) by rewrite ler_wpM2l // lerDl.
  exact: le_lt_trans h2 h1.
split; first exact: (@ddg_flow_injective R n (smooth_test_value hE g) K hK t htK).
exact: (@ddg_flow_immersion R n (smooth_test_value hE g) Dg hg K hK M t hK0 hM htK).
Qed.

(** Source for [dgpr_first_variation]: blueprint lem:first_variation:
    if V is a k dimensional varifold in R^n with ‖V‖(R^n) < ∞,
    g ∈ D(R^n, R^n) has the differentials Dg(x), and F is of class 1
    relative to G(n, k), then δ_F V(g) exists and
    δ_F V(g) = ∫ B_F(S) • Dg(x) dV(x, S). This is DDG Lemma A.2, (A.9),
    p. 1144, for an integrand not depending on the point. Direct
    formalisation. *)
Theorem dgpr_first_variation (V : set GB -> \bar R) (F : Hom Rn Rn -> R)
    (g : smooth_test_space hE) (Dg : Rn -> Hom Rn Rn) :
  is_varifold V -> (V setT < +oo)%E -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  (forall x, has_norm_differential Nn Nn setT (smooth_test_value hE g) x (Dg x)) ->
  exists c : R, is_dgpr_first_variation V F (smooth_test_value hE g) Dg c /\
    is_measure_integral V
      (real_total_integrand (fun z : GB => HI (dgpr_B k F (set_val z.2 : Hom Rn Rn)) (Dg z.1))) c%:E.
Proof.
move=> hV hVf hF hD.
have hg := dgpr_test_class_one hD.
have [K hK0 hK] := dgpr_test_lipschitz g.
have [M hM] := dgpr_test_bounded g.
have [Lam hLam hFL] := dgpr_integrand_lipschitz hF.
have [Phi hPhi] := dgpr_integrand_bounded hF.
have [delta [c [hdelta hc hE' hI]]] := ddg_lemma_A_2_constant_lipschitz hV hVf hg hK0 hK hM hLam
  hFL hPhi (fun T hT => dgpr_integrand_differentiable hF hT).
exists c; split => //.
by exists delta.
Qed.

End FirstVariation.

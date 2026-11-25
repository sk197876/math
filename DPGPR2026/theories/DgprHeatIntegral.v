(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, proof
    of Lemma 3.1; blueprint dgpr_blueprint.tex, proof of lem:DGPR31: if
    f : Omega_T -> R has Gaussian decay before T and H f = h on Omega_T,
    then [t |-> ∫ f(t,x) dL^n x] is of class 1 on R ∩ {t : t < T}, with
    derivative [t |-> ∫ h(t,x) dL^n x].

    The proof combines lem:classes(cl:dt) (DgprClassesTimeDerivative.v)
    and lem:classes(cl:div) (DgprDivergenceIntegral.v) with the jets of
    DgprHeatJets.v. The time derivative in a jet is D f(t,x)(1,0) by the
    chain rule (Federer 3.1.1, p. 210); the Laplacian in a jet is the
    trace of the second differential of the section [x |-> f(t,x)]
    (Federer 3.1.11, p. 219). The section has Gaussian decay, because
    its kth differential is the kth differential of f composed with the
    isometry [x |-> (0,x)] in every argument (chain rule of 3.1.11 for
    the affine map [x |-> (t,x)], DgprBackwardHeatDecay.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerProductUP ScalarInnerProduct ProductInner
  ProductInnerPairRegularity NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic
  NormDifferentialChain NormDifferentialLocal NormDifferentialScalar NormOpenDomainLaws
  NormDifferentialDirectional
  NormedCurveDerivativeUP NormHigherCurveDerivativeUP
  NormClassOneUP NormRegularity NormRegularityOperations NormClassHigherUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialFirst
  MultilinearSuccessorArguments
  PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic EuclideanLebesgueDimensions.
From DPGPR Require Import DgprGrowthClasses DgprDifferentialCalculus DgprParameterIntegralSmooth
  DgprHeatJets DgprHeatJetCalculus DgprBackwardHeatDecay DgprClassesTimeDerivative
  DgprDivergenceIntegral DgprIntegrationByPartsClasses DgprIdentitiesSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HeatIntegral.
Variable R : realType.
Variable n : nat.
Variable T : R.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation eps := (@coordinate_basis R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R)
  (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Local Notation e0 := (((1 : R^o), (0 : X)) : TX).
Local Notation Zt k := (@ContinuousMultilinear.space R k TX R^o NT A1 hNT hA).
Local Notation evt k := (@ContinuousMultilinear.evaluation R k TX R^o NT A1 hNT hA).
Local Notation ZNt k := (@ContinuousMultilinear.norm R k TX R^o NT A1 hNT hA).
Local Notation lawst k := (@ContinuousMultilinear.laws R k TX R^o NT A1 hNT hA).
Local Notation Zs k := (@ContinuousMultilinear.space R k X R^o N A1 hN hA).
Local Notation evs k := (@ContinuousMultilinear.evaluation R k X R^o N A1 hN hA).
Local Notation ZNs k := (@ContinuousMultilinear.norm R k X R^o N A1 hN hA).
Local Notation lawss k := (@ContinuousMultilinear.laws R k X R^o N A1 hN hA).

(** Source for [dgpr_space_injection]: the linear map [x |-> (0,x)] of
    R^n into R x R^n (Federer 1.7.11, p. 36). *)
Definition dgpr_space_injection : Hom X TX := @product_second_injection_hom R R^o X.

(** Source for [dgpr_space_injection_bound]: the map [x |-> (0,x)] is an
    isometry for the product inner product of Federer 1.7.11, p. 36. *)
Lemma dgpr_space_injection_bound (x : X) : NT (dgpr_space_injection x) <= 1 * N x.
Proof.
rewrite mul1r /dgpr_space_injection.
by rewrite (product_second_injection_norm (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Qed.

(** Source for [dgpr_space_affine]: (0,x) + (t,0) = (t,x) in R x R^n. *)
Lemma dgpr_space_affine (t : R) (x : X) :
  dgpr_space_injection x + ((t : R^o), (0 : X)) = ((t : R^o), x).
Proof.
apply: injective_projections => /=.
- by change ((0 : R^o) + t = t); rewrite add0r.
- by change (x + 0 = x); rewrite addr0.
Qed.

(** Source for [dgpr_slice_class]: the section [x |-> f(t,x)] of a map
    of class k on Omega_T is of class k on R^n for t < T, by the chain
    rule of Federer 3.1.11, p. 220, for the affine map [x |-> (t,x)]. *)
Lemma dgpr_slice_class (f : TX -> R) (t : R) (k : nat) : t < T ->
  norm_class hNT hA (dgpr_before T) f k -> norm_class hN hA setT (fun x => f (t, x)) k.
Proof.
move=> ht hf.
have hLb : norm_bounded_linear N NT dgpr_space_injection.
  by exists 1; split => // x; exact: dgpr_space_injection_bound.
have hL := norm_class_linear hN hNT k (fun x _ => norm_full_domain_interior N x) hLb.
have hC := norm_class_constant hN hNT (((t : R^o), (0 : X)) : TX) k
  (fun x _ => norm_full_domain_interior N x).
have hAff : norm_class hN hNT setT (fun x : X => (((t : R^o), x) : TX)) k.
  apply: (norm_class_domain_agreement _ (norm_class_add hL hC)) => x _.
  exact: dgpr_space_affine.
exact: (norm_class_compose_on (fun x _ => ht) hAff hf).
Qed.

(** Source for [dgpr_slice_gaussian]: if f has Gaussian decay before T
    (def:classes), then the section [x |-> f(t,x)] has Gaussian decay for
    t < T: its kth differential at x is the kth differential of f at
    (t,x) composed with the isometry [x |-> (0,x)] in every argument
    (Federer 3.1.11, chain rule), and the strip [t,t] is admissible. *)
Lemma dgpr_slice_gaussian (f : TX -> R) (t : R) : t < T ->
  dgpr_gaussian_decay_before hA T f -> dgpr_gaussian_decay hA (fun x => f (t, x)).
Proof.
move=> ht [hcls hdec]; split; first by move=> k; exact: (dgpr_slice_class ht (hcls k)).
move=> j; have [c [hc hb]] := hdec j t t ht.
exists c; split => // x z _ hz.
have [_ [D [hD _]]] := hcls j.
have [Pk [hPk hPkb]] := @dgpr_pullback_hom R X TX R^o N NT A1 hN hNT hA
  dgpr_space_injection 1 ler01 dgpr_space_injection_bound j.
have hxp p : dgpr_before T (dgpr_space_injection p + ((t : R^o), (0 : X))).
  by rewrite dgpr_space_affine.
have hx := hxp x.
have hpull := @dgpr_higher_differential_pullback R X TX R^o N NT A1 hN hNT hA
  dgpr_space_injection 1 ler01 dgpr_space_injection_bound ((t : R^o), (0 : X)) (dgpr_before T)
  (@dgpr_before_open R n T) f j D Pk hPk hD x hx.
have eA : (fun p : X => dgpr_before T (dgpr_space_injection p + ((t : R^o), (0 : X)))) = setT.
  by apply: funext => p; apply: propext; split => // _; exact: hxp.
have ef : (fun p : X => f (dgpr_space_injection p + ((t : R^o), (0 : X)))) = (fun p => f (t, p)).
  by apply: funext => p; rewrite dgpr_space_affine.
rewrite eA ef dgpr_space_affine in hpull.
have ez := norm_higher_differential_unique hN hA (fun k => lawss k) hz hpull.
rewrite ez; apply: le_trans (hPkb _) _.
rewrite expr1n mul1r; apply: (hb (t, x)); first by rewrite /dgpr_time_strip /= lexx.
exact: hD.
Qed.

(** Source for [dgpr_time_derivative_differential]: if D G(t,x) = L on
    Omega_T, then the curve [r |-> G(r,x)] has derivative L(1,0) at t,
    by the chain rule of Federer 3.1.1, p. 210, for the affine curve
    [r |-> (r,x)]. *)
Lemma dgpr_time_derivative_differential (W : lmodType R) (NW : W -> R) (hNW : is_real_norm NW)
    (G : TX -> W) (t : R) (x : X) (L : Hom TX W) : t < T ->
  has_norm_differential NT NW (dgpr_before T) G (t, x) L ->
  has_normed_curve_derivative NW (fun r => G (r, x)) t (L e0).
Proof.
move=> ht hG.
pose M : Hom R^o TX := @product_first_injection_hom R R^o X.
pose bx : TX := ((0 : R^o), x).
have hM r : M r + bx = (r, x).
  apply: injective_projections => /=.
  - by change (r + 0 = r); rewrite addr0.
  - by change ((0 : X) + x = x); rewrite add0r.
have hMb : norm_bounded_linear A1 NT M.
  exists 1; split => // r; rewrite mul1r.
  by rewrite (product_first_injection_norm (scalar_inner_productP R) (@euclidean_inner_productP R n))
    scalar_inner_normE.
have hc : has_norm_differential A1 NT (fun _ => True) (fun r : R^o => M r + bx) t (M + 0).
  exact: (norm_differential_add hNT (norm_differential_linear hA hNT (norm_full_domain_interior A1 t) hMb)
    (norm_differential_constant hA hNT bx (norm_full_domain_interior A1 t))).
rewrite -(hM t) in hG.
have hch := norm_differential_chain hA hNT hNW hc hG.
have [_ hcur] := (@norm_differential_real_source R W NW hNW _ _ t _).1 hch.
have ef : (fun r : R => G (M r + bx)) = (fun r => G (r, x)) by apply: funext => r; rewrite hM.
rewrite ef in hcur.
have e1 : hom_comp L (M + 0) 1 = L e0.
  rewrite hom_compE; congr (L _); apply: injective_projections => /=.
  - by change (1 + 0 = 1 :> R); rewrite addr0.
  - by change ((0 : X) + 0 = 0); rewrite addr0.
by rewrite e1 in hcur.
Qed.

(** Source for [dgpr_heat_integral]: proof of lem:DGPR31, blueprint
    section 4 (the step J'(t) = ∫ H(rho log q)(t,x) dL^n x and its
    analogue for rho |B|^2): if f has Gaussian decay before T and
    H f = h on Omega_T, then for t < T the sections f_t and h_t are L^n
    summable and [t |-> ∫ f_t dL^n] is of class 1 on R ∩ {t : t < T} with
    derivative [t |-> ∫ h_t dL^n]; lem:classes(cl:dt) and (cl:div). *)
Theorem dgpr_heat_integral (f h : TX -> R) :
  dgpr_gaussian_decay_before hA T f ->
  (forall t x, t < T -> dgpr_heat_operator A1 f t x (h (t, x))) ->
  exists I H : R -> R,
    [/\ forall t, t < T -> is_measure_integral LL (real_total_integrand (fun x => f (t, x))) (I t)%:E,
        forall t, t < T -> is_measure_integral LL (real_total_integrand (fun x => h (t, x))) (H t)%:E &
        is_norm_class_one_field A1 A1 [set t | t < T] I (fun t => dgpr_line_hom (H t : R^o))].
Proof.
move=> hg hH; have [hcls _] := hg.
have [_ [D1 [hD1 _]]] := hcls 1%N.
have hex p : exists L : Hom TX R^o, dgpr_before T p ->
    has_norm_differential NT A1 (dgpr_before T) f p L.
  case: (pselect (dgpr_before T p)) => hp; last by exists 0.
  have h1 := (@norm_higher_differential_first R TX R^o NT A1 hNT hA (fun k => Zt k)
    (fun k => evt k) (fun k => ZNt k) (fun k => lawst k) (dgpr_before T) f p (D1 p)).1 (hD1 p hp).
  by eexists => _; exact: h1.
case: (choice hex) => Df hDf.
have [hsum hclass] := dgpr_classes_dt hg hDf.
have hsplit t : t < T -> exists lap : X -> R,
    is_measure_integral LL (real_total_integrand lap) 0%:E /\
    forall x, h (t, x) = Df (t, x) e0 + lap x.
  move=> ht; have hgs := dgpr_slice_gaussian ht hg.
  have [_ [D1s [hD1s _]]] := hgs.1 1%N.
  have [_ [D2s [hD2s _]]] := hgs.1 2%N.
  have hD1s' x : dgpr_higher_differential hN hA setT (fun x => f (t, x)) 1 x (D1s x) := hD1s x I.
  have hD2s' x : dgpr_higher_differential hN hA setT (fun x => f (t, x)) 2 x (D2s x) := hD2s x I.
  have [E [hE hEv]] := dgpr_second_differential_fields hD1s' hD2s'.
  exists (fun x => dgpr_laplacian (D2s x)); split; first exact: (dgpr_classes_laplacian hgs hD2s').
  move=> x; have [a [Dfv [D2v [[ha [hDfv hD2v]] ->]]]] := hH t x ht.
  have hcur := dgpr_time_derivative_differential hA ht (hDf (t, x) ht).
  have ea : a = Df (t, x) e0.
    have e := norm_differential_unique hA hA (dgpr_curve_to_differential hA ha)
      (dgpr_curve_to_differential hA hcur).
    have := congr1 (fun L : Hom R^o R^o => L 1) e.
    by rewrite /= !scale1r.
  have hDfvE y w : Dfv y w = continuous_multilinear_one_operator (lawss 1) (D1s y) w.
    apply: (dgpr_differential_values_unique hA (hDfv y)).
    exists (continuous_multilinear_one_operator (lawss 1) (D1s y)); split => //.
    exact: dgpr_first_differential_operator (hD1s' y).
  have hD2vE v w : D2v v w = evs 2 (multilinear_successor_arguments [ffun _ : 'I_1 => w] v) (D2s x).
    have h1 := hD2v w.
    have ef : (fun y => Dfv y w) = (fun y => continuous_multilinear_one_operator (lawss 1) (D1s y) w).
      by apply: funext => y; exact: hDfvE.
    rewrite ef in h1.
    by rewrite (dgpr_differential_values_unique hA h1 (hE x w) v) hEv.
  rewrite ea /dgpr_laplacian_values /dgpr_laplacian; congr (_ + _).
  apply: eq_bigr => i _; rewrite hD2vE dgpr_two_arguments; congr (evs 2 _ _).
  by apply/ffunP => k; rewrite !ffunE; case: ifP.
have hIex t : exists v : R, t < T ->
    is_measure_integral LL (real_total_integrand (fun x => f (t, x))) v%:E.
  case: (pselect (t < T)) => ht; last by exists 0.
  by have [v hv] := (hsum t ht).1; exists v.
have hDIex t : exists v : R, t < T ->
    is_measure_integral LL (real_total_integrand (fun x => Df (t, x) e0)) v%:E.
  case: (pselect (t < T)) => ht; last by exists 0.
  by have [v hv] := (hsum t ht).2; exists v.
case: (choice hIex) => I hI; case: (choice hDIex) => DI hDI.
exists I, DI; split => //; last exact: (hclass I DI hI hDI).
move=> t ht; have [lap [hlap he]] := hsplit t ht.
have hs := real_total_integral_add hLL (hDI t ht) hlap.
rewrite addr0 in hs.
have ef : (fun x => h (t, x)) = (fun x => Df (t, x) e0 + lap x) by apply: funext => x; exact: he.
by rewrite ef.
Qed.

End HeatIntegral.

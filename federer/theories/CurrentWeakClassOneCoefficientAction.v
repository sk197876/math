(** Federer (1969), 4.1.19, p. 377: compare
    a measurable weak derivative with the actual
    derivative of a class-one form. The original
    compact smooth probes extend to each compact L1
    coefficient separately. The derivative is localized only
    inside this proof, never bounded on all U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import AlternatingForms Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingPairing
  ExteriorDerivativeUP CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  CompactSummableFieldExtensionality CompactSummableFieldLaws
  CurrentLonePairImageUP CurrentLonePairCost SmoothCompactSet SmoothFunctionSupport
  SmoothCurrentDivergence EuclideanOpenDomainMeasure EuclideanClosedSupportTube
  CurrentCompactTubeIndex CurrentCompactClosedTubeInside
  CurrentCompactSmoothDivergenceExistence CurrentCompactSmoothDivergenceSupport
  CurrentWeakExteriorPairUP FlatCochainRepresentationUP BoundedPairFormFunctional
  WeakExteriorPairGraphAction CurrentClassOneWeakExterior
  CurrentClassOneBoundedReplacement CompactSummableSmoothApproximation
  SeminormFunctionalClosedKernel MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClassOneCoefficientActions.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation O := (@compact_summable_multivector_space R h2 n m.+1 U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation size := (@compact_summable_multivector_size R h2 n m.+1 U hU).
Local Notation hSize := (@compact_summable_multivector_size_laws R h2 n m.+1 U hU).
Local Notation support := (@compact_summable_multivector_ambient_support R h2 n m.+1 U hU).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [current_weak_class_one_coefficient_actions]:
    the class-one assertion of Federer 4.1.19,
    p. 377, first identifies both original
    Omega_(m+1) integral actions. The original bounded
    measurability of phi and psi is retained;
    boundedness of the actual derivative on U,
    finite ambient volume and normality are not added. *)
Theorem current_weak_class_one_coefficient_actions
    (phi : X -> Y m) (beta : X -> Y m.+1) (psi : UT -> Y m.+1) :
  norm_class hNX (@current_form_comass_real_norm R h2 n m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative NX
    (@current_form_comass R h2 n m) U phi x (beta x)) ->
  @is_bounded_measurable_current_form R h2 n U m
    (fun x : UT => phi (set_val x)) ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  @is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x)) psi ->
  forall xi : O, exists r : R,
    is_measure_integral mu (real_total_integrand (fun x : UT =>
      pairing (value m.+1 xi x) (beta (set_val x)))) r%:E /\
    is_measure_integral mu (real_total_integrand (fun x : UT =>
      pairing (value m.+1 xi x) (psi x))) r%:E.
Proof.
move=> hClass hActual hPhi hPsi hWeak xi.
have [F [cF [hCF [hFBound hFDensity]]]] :=
  @bounded_pair_form_functional_exists R h2 n m U hU
    (fun x : UT => phi (set_val x)) psi hPhi hPsi.
have hFGraph := (@weak_exterior_pair_graph_action_iff R h2 n m U hU F
  (fun x : UT => phi (set_val x)) psi hFDensity).1 hWeak.
have hCarrier := @compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU xi.
pose K0 := @Build_smooth_compact_set R X NX hNX U (support xi)
  hCarrier.2.1 hCarrier.1.
have [delta [hDelta hInside]] := @current_compact_closed_tube_inside_exists R n U hU K0.
pose K := @current_compact_closed_tube_index R n U K0 delta hInside.
have hK0 : smooth_compact_carrier K0 `<=` smooth_compact_carrier K.
  exact: (@current_compact_closed_tube_index_includes R n U K0 delta hInside (ltW hDelta)).
have [chi [b [hChi [hBActual [hChiBounded [hBBounded hAgreement]]]]]] :=
  @current_class_one_bounded_replacement R h2 n m U hU K phi beta hClass hActual.
have [G [cG [hCG [hGBound hGDensity]]]] :=
  @bounded_pair_form_functional_exists R h2 n m U hU
    (fun x : UT => chi (set_val x))
    (fun x : UT => b (set_val x)) hChiBounded hBBounded.
have hGWeak := @current_class_one_exterior_weak_integral R h2 n m U hU
  chi b hChi hBActual.
have hGGraph := (@weak_exterior_pair_graph_action_iff R h2 n m U hU G
  (fun x : UT => chi (set_val x))
  (fun x : UT => b (set_val x)) hGDensity).1 hGWeak.
have hRightLinear : linear (fun eta : O => ((0,eta):P)).
  move=> a eta zeta.
  change (((0 : @compact_summable_multivector_space R h2 n m U hU),
      a*:eta+zeta)=(a*:(0 : @compact_summable_multivector_space R h2 n m U hU)+0,
      a*:eta+zeta)).
  by rewrite scaler0 add0r.
pose right := @HomMap R O P (fun eta => (0,eta))
  (introT (asboolP _) hRightLinear).
pose H : Hom O R^o := hom_comp (F-G)%R right.
have hHValue (eta : O) : H eta=F (0,eta)-G (0,eta).
  by [].
have hHBound (eta : O) : `|H eta| <= (cF+cG)*size eta.
  have hF := hFBound (0,eta).
  have hG := hGBound (0,eta).
  rewrite /current_lone_pair_cost /=
    (real_seminorm_zero (@compact_summable_multivector_size_laws R h2 n m U hU))
    add0r in hF hG.
  rewrite hHValue mulrDl.
  exact: (le_trans (ler_normB _ _) (lerD hF hG)).
pose A : set O := [set zeta | exists eta : @current_vector_smooth_space R h2 n U hU m.+1,
  @smooth_function_support R X (exterior_power X m.+1) NX hNX U
    (@current_vector_smooth_space R h2 n U hU m.+1) (ev m.+1) eta
      `<=` smooth_compact_carrier K /\
  value m.+1 zeta=(fun x : UT => ev m.+1 eta (set_val x))].
have hZero (zeta : O) : A zeta -> H zeta=0.
  move=> [eta [hSupport hZeta]].
  have [v [hGraph [hLeft [hRight hOff]]]] :=
    @current_compact_smooth_divergence_pair_exists R h2 n m U hU K eta hSupport.
  have hV2 : v.2=zeta.
    apply: (@compact_summable_field_value_injective R UT (exterior_power X m.+1)
      (@current_vector_mass R h2 n m.+1) (@current_vector_mass_real_norm R h2 n m.+1)
      mu hMu).
    change (value m.+1 v.2=value m.+1 zeta).
    by rewrite hRight hZeta.
  have hDivSupport := @current_compact_smooth_divergence_support R h2 n m U hU
    K eta hSupport.
  have hFirst : F (v.1,0)=G (v.1,0).
    have hLeftF := hFDensity.2.2.1 v.1.
    have hLeftG := hGDensity.2.2.1 v.1.
    have hPoint : (fun x : UT => pairing (value m v.1 x) (phi (set_val x)))=
        (fun x : UT => pairing (value m v.1 x) (chi (set_val x))).
      apply: funext=> x; have [hx|hx] := pselect (smooth_compact_carrier K (set_val x)).
      - by rewrite (@hAgreement (set_val x) hx).1.
      - have hDiv := (smooth_function_compact_support_iff (hE m) K (div eta)).1
          hDivSupport (set_val x) hx.
        by rewrite hLeft hDiv /pairing !linear0.
    rewrite hPoint in hLeftF.
    exact: (EFin_inj (measure_integral_unique hLeftF hLeftG)).
  have hFV := hFGraph v hGraph.
  have hGV := hGGraph v hGraph.
  have hPair : ((v.1,0):P)+(0,v.2)=v.
    apply: injective_projections.
    - change (v.1+0=v.1); exact: addr0.
    - change (0+v.2=v.2); exact: add0r.
  have hFAdd := linD (hom_linear F) (v.1,0) (0,v.2).
  have hGAdd := linD (hom_linear G) (v.1,0) (0,v.2).
  rewrite hPair hV2 in hFAdd hGAdd.
  rewrite hHValue.
  lra.
have hApprox tolerance (hTolerance : 0<tolerance) :
    exists zeta : O, A zeta /\ size (xi-zeta)%R<tolerance.
  have [eta [zeta [hSupport [hValue hError]]]] :=
    @compact_summable_smooth_approximation_on_carrier R h2 n m.+1 U hU
      xi delta K hDelta (fun x hx => hx) tolerance hTolerance.
  exists zeta; split; last exact: hError.
  by exists eta.
have hHZero := @seminorm_functional_annihilates_closure R O size H
  (cF+cG) A xi (addr_ge0 hCF hCG) hHBound hZero hApprox.
have hSame : F (0,xi)=G (0,xi).
  rewrite hHValue in hHZero.
  by apply/eqP; rewrite -subr_eq0; apply/eqP.
have hBIntegral := hGDensity.2.2.2 xi.
rewrite -hSame in hBIntegral.
have hPoint : (fun x : UT => pairing (value m.+1 xi x) (b (set_val x)))=
    (fun x : UT => pairing (value m.+1 xi x) (beta (set_val x))).
  apply: funext=> x.
  have [hx|hx] := pselect (smooth_compact_carrier K0 (set_val x)).
  - by rewrite (@hAgreement (set_val x) (@hK0 (set_val x) hx)).2.
  - have hOff : value m.+1 xi x=0.
      rewrite -(compact_summable_multivector_ambient_inside xi x).
      have hOutside := hCarrier.2.2.
      exact: (@hOutside (set_val x) hx).
    by rewrite hOff /pairing !linear0.
rewrite hPoint in hBIntegral.
exists (F (0,xi)); split; first exact: hBIntegral.
exact: (hFDensity.2.2.2 xi).
Qed.
End ClassOneCoefficientActions.

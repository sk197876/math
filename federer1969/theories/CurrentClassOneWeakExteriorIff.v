(** Federer (1969), 4.1.19, p. 377: identify
    the measurable second form with the actual
    exterior derivative of a class-one first form.
    The original weak integrals determine its almost
    class, as required for arbitrary measurable representatives. *)
From mathcomp Require Import functions all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity NormClassZeroTopology NormClassHigherDerivative InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorDerivativeUP
  CurrentDomain CurrentCoefficientNorms CurrentClassOneExterior
  CurrentContinuousFormMeasurable CompactMultivectorFormUniqueness
  CurrentWeakClassOneCoefficientAction CurrentWeakExteriorPairUP
  WeakExteriorPairAlmostEquality EuclideanOpenDomainMeasure
  FlatCochainRepresentationUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClassOneWeakEquivalence.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [current_class_one_weak_exterior_iff]:
    the class-one parenthesis of Federer 4.1.19,
    p. 377, on the original U.
    For an arbitrary measurable psi the conclusion
    is almost equality with the actual derivative;
    no continuity or chosen pointwise values of
    psi, or global derivative bound, is added. *)
Theorem current_class_one_weak_exterior_iff
    (phi : X -> Y m) (beta : X -> Y m.+1) (psi : UT -> Y m.+1) :
  norm_class hNX (hN m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative NX (N m) U phi x (beta x)) ->
  @is_bounded_measurable_current_form R h2 n U m
    (fun x : UT => phi (set_val x)) ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  (@is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x)) psi <->
    measure_almost_everywhere mu [set x | beta (set_val x)=psi x]).
Proof.
move=> hClass hActual hPhi hPsi; split.
- move=> hWeak.
  have [gamma [hGamma hGammaActual]] := @current_class_one_exterior_continuous
    R h2 n m U phi hClass.
  have hSame (x : X) (hx : U x) : gamma x=beta x.
    exact: (exterior_derivative_unique hNX (hN m)
      (@hGammaActual x hx) (@hActual x hx)).
  have hContinuous := norm_class_zero_domain_agreement hSame hGamma.
  have hMeas := @current_continuous_form_normed_measurable R h2 n m.+1 U hU
    beta hContinuous.
  have hActions := @current_weak_class_one_coefficient_actions R h2 n m U hU
    phi beta psi hClass hActual hPhi hPsi hWeak.
  exact: (@compact_multivector_form_density_almost_unique R h2 n m.+1 U hU
    (fun x : UT => beta (set_val x)) psi hMeas hPsi.1 hActions).
- exact: (@current_class_one_almost_derivative_weak R h2 n m U hU
    phi beta psi hClass hActual).
Qed.

(** Source for [current_class_one_weak_exterior_graph_iff]:
    the same original class-one criterion in
    Federer 4.1.19, p. 377, stated
    with the actual partial exterior-derivative graph.
    A caller supplies no chosen derivative field;
    every natural degree and the empty U remain. *)
Theorem current_class_one_weak_exterior_graph_iff
    (phi : X -> Y m) (psi : UT -> Y m.+1) :
  norm_class hNX (hN m) U phi 1%N ->
  @is_bounded_measurable_current_form R h2 n U m
    (fun x : UT => phi (set_val x)) ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  (@is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x)) psi <->
    measure_almost_everywhere mu [set x : UT |
      has_exterior_derivative NX (N m) U phi (set_val x) (psi x)]).
Proof.
move=> hClass hPhi hPsi.
have [beta [hContinuous hActual]] := @current_class_one_exterior_continuous
  R h2 n m U phi hClass.
have hIff := @current_class_one_weak_exterior_iff phi beta psi
  hClass hActual hPhi hPsi.
split.
- move=> hWeak.
  have hAlmost := hIff.1 hWeak.
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hAlmost)=> x hx.
  change (has_exterior_derivative NX (N m) U phi (set_val x) (psi x)).
  have hEqual : beta (set_val x)=psi x := hx.
  rewrite -hEqual; exact: (@hActual (set_val x) (set_valP x)).
- move=> hGraph; apply: hIff.2.
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hGraph)=> x hx.
  exact: (exterior_derivative_unique hNX (hN m)
    (@hActual (set_val x) (set_valP x)) hx).
Qed.
End ClassOneWeakEquivalence.

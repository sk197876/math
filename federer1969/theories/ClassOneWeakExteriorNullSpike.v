(** Federer (1969), 4.1.19, p. 377: a
    supporting representative test for the class-one
    parenthesis. The first form is the actual
    smooth zero form. A nonzero one-form at
    one Lebesgue-null point preserves the original weak
    equation while changing the pointwise derivative graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates ExteriorGrading AlternatingForms EuclideanCoordinateForms
  ExteriorDerivativeUP ExteriorDifferentialSealed CurrentDomain CurrentCoefficientNorms
  CurrentWeakExteriorPairUP CurrentClassOneWeakExterior WeakExteriorPairAlmostEquality
  FlatCochainRepresentationUP BoundedCurrentFormZero EuclideanOpenDomainMeasure
  EuclideanFullDomainMeasure EuclideanLebesgueDimensions ApproximateDifferentialAffine
  MeasureUP MeasurePushforward MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality PartialFunctionBasic MeasurableNormedFunctionUP MeasurableNormedBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClassOneNullSpike.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation UT := (current_domain R 1%N Full).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 1%N d).
Local Notation hN d := (@current_form_comass_real_norm R h2 1%N d).
Local Notation mu := (@euclidean_open_domain_measure R 1%N Full).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R 1%N Full hFull)).

(** Source for [class_one_weak_exterior_null_spike]:
    the class-one input in Federer 4.1.19,
    p. 377, stays literal in this
    test: phi is smooth everywhere. Both original
    forms are bounded measurable, and the exact
    weak integral holds, although the chosen psi
    differs from the actual derivative at one point. *)
Theorem class_one_weak_exterior_null_spike :
  exists phi : X -> Y 0%N, exists psi : X -> Y 1%N,
    norm_class_all_orders hNX (hN 0%N) Full phi /\
    @is_bounded_measurable_current_form R h2 1%N Full 0%N
      (fun x : UT => phi (set_val x)) /\
    @is_bounded_measurable_current_form R h2 1%N Full 1%N
      (fun x : UT => psi (set_val x)) /\
    @is_weak_current_exterior_pair R h2 1%N 0%N Full hFull
      (fun x : UT => phi (set_val x)) (fun x : UT => psi (set_val x)) /\
    exists x : X, ~has_exterior_derivative NX (N 0%N) Full phi x (psi x).
Proof.
pose phi := fun _ : X => (0:Y 0%N).
pose theta := @euclidean_coordinate_form R 1%N ord0.
pose psi := fun x : X => if pselect (x=0) then theta else (0:Y 1%N).
have hThetaValue : theta [tuple @coordinate_basis R 1%N ord0]= 1.
  by rewrite /theta euclidean_coordinate_form_dual eqxx.
have hThetaNonzero : theta<>0.
  move=> hZero.
  have hImpossible := hThetaValue.
  rewrite hZero form_zeroE in hImpossible.
  move/eqP: hImpossible; by rewrite eq_sym oner_eq0.
have hSmooth : norm_class_all_orders hNX (hN 0%N) Full phi.
  move=> k; exact: (@norm_class_constant R X (Y 0%N) NX (N 0%N)
    hNX (hN 0%N) Full 0 k hFull).
have hActual (x : X) (_ : Full x) :
    has_exterior_derivative NX (N 0%N) Full phi x (0:Y 1%N).
  exists (0:Hom X (Y 0%N)); split.
  - exact: (@norm_differential_constant R X (Y 0%N) NX (N 0%N)
      hNX (hN 0%N) Full x 0 (@hFull x Logic.I)).
  - have hValue := @ExteriorDifferential.laws R h2 1%N R^o 0%N
      (0:Hom X (Y 0%N)).
    have hZero := lin0 (@exterior_differential_linear R h2 1%N R^o 0%N).
    by rewrite hZero in hValue.
pose p := @euclidean_full_domain_point R 1%N.
pose a : UT := p 0.
have hNull : mu [set a]=0%E.
  change (@euclidean_full_domain_measure R 1%N [set a]=0%E).
  rewrite euclidean_full_domain_measure_image /measure_pushforward.
  have hSet : p @^-1` [set a]=[set (0:X)].
    apply/seteqP; split.
    - move=> x hx.
      change (p x=a) in hx; change (x=0).
      have hPoint := congr1 (set_val : UT -> X) hx.
      exact hPoint.
    - move=> x hx; change (x=0) in hx; by rewrite hx.
  rewrite hSet; exact: (@positive_euclidean_singleton_null R 0%N (0:X)).
have hAlmost : measure_almost_everywhere mu
    [set x : UT | (0:Y 1%N)=psi (set_val x)].
  have hConull : measure_almost_everywhere mu (~` [set a]).
    by rewrite /measure_almost_everywhere setCK.
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hConull)=> x hx.
  have hOff : set_val x<>(0:X).
    move=> hPoint; apply: hx; apply: val_inj; exact: hPoint.
  change ((0:Y 1%N)=psi (set_val x)).
  rewrite /psi; case: (pselect (set_val x=0))=> hPoint; last exact: erefl.
  exfalso; exact: hOff hPoint.
have hPartial : measure_almost_equal mu
    (partial_function_total (fun _ : UT => (0:real_norm_metric_space (hN 1%N))))
    (partial_function_total (fun x : UT =>
      (psi (set_val x):real_norm_metric_space (hN 1%N)))).
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hAlmost)=> x hx.
  exists (0:Y 1%N); split; first exact: erefl.
  exact: esym hx.
have hMeas := @measurable_normed_almost_equal R UT (Y 1%N) (N 1%N) (hN 1%N)
  mu hMu _ _ (@measurable_normed_total_constant R UT (Y 1%N) (N 1%N)
    (hN 1%N) mu hMu 0) hPartial.
have hPsiBounded : @is_bounded_measurable_current_form R h2 1%N Full 1%N
    (fun x : UT => psi (set_val x)).
  split; first exact: hMeas.
  exists (N 1%N theta); split; first exact: real_seminorm_nonnegative (hN 1%N).1 theta.
  move=> x; rewrite /psi; case: (pselect (set_val x=0))=> hPoint.
  - exact: lexx.
  - rewrite (real_seminorm_zero (hN 1%N).1).
    exact: real_seminorm_nonnegative (hN 1%N).1 theta.
have hPhiBounded := @bounded_measurable_current_form_zero R h2 1%N 0%N Full hFull.
have hWeak := @current_class_one_almost_derivative_weak R h2 1%N 0%N Full hFull
  phi (fun _ : X => (0:Y 1%N)) (fun x : UT => psi (set_val x))
  (hSmooth 1%N) hActual hAlmost.
exists phi,psi; split; first exact: hSmooth.
split; first exact: hPhiBounded.
split; first exact: hPsiBounded.
split; first exact: hWeak.
exists (0:X); move=> hDerivative.
have hEqual := exterior_derivative_unique hNX (hN 0%N)
  (@hActual (0:X) Logic.I) hDerivative.
have hAtPoint : psi (0:X)=theta by rewrite /psi; case: pselect=> //.
rewrite hAtPoint in hEqual; exact: hThetaNonzero (esym hEqual).
Qed.
End ClassOneNullSpike.

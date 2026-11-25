(** Federer (1969), 4.1.19, p. 377: the
    pointwise class-one weak-derivative criterion for continuous
    second representatives. The original theorem for merely
    measurable representatives remains the almost-everywhere statement;
    continuity gives this separate exact upgrade. *)
From mathcomp Require Import functions all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorDerivativeUP CurrentDomain CurrentCoefficientNorms
  CurrentClassOneExterior CurrentClassOneWeakExteriorIff
  CurrentWeakExteriorPairUP FlatCochainRepresentationUP
  EuclideanContinuousAlmostEquality EuclideanOpenDomainMeasure
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_class_one_weak_exterior_pointwise_iff]:
    the pointwise reading of the class-one
    parenthesis in Federer 4.1.19, p. 377,
    when psi is continuous. The actual
    exterior derivative graph is used at
    every original U point; no global
    derivative bound is added. *)
Theorem current_class_one_weak_exterior_pointwise_iff
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (phi : R_n R n -> A_m (R_n R n) R^o m)
    (psi : R_n R n -> A_m (R_n R n) R^o m.+1) :
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@current_form_comass_real_norm R h2 n m) U phi 1%N ->
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n m.+1) U psi ->
  @is_bounded_measurable_current_form R h2 n U m
    (fun x : current_domain R n U => phi (set_val x)) ->
  @is_bounded_measurable_current_form R h2 n U m.+1
    (fun x : current_domain R n U => psi (set_val x)) ->
  (@is_weak_current_exterior_pair R h2 n m U hU
    (fun x : current_domain R n U => phi (set_val x))
    (fun x : current_domain R n U => psi (set_val x)) <->
    forall x, U x -> has_exterior_derivative
      (inner_norm (@euclidean_inner_productP R n))
      (@current_form_comass R h2 n m) U phi x (psi x)).
Proof.
move=> hClass hPsiContinuous hPhi hPsi.
have [beta [hBetaContinuous hActual]] := @current_class_one_exterior_continuous
  R h2 n m U phi hClass.
have hIff := @current_class_one_weak_exterior_iff R h2 n m U hU
  phi beta (fun x : current_domain R n U => psi (set_val x))
  hClass hActual hPhi hPsi.
split.
- move=> hWeak.
  have hAlmost := hIff.1 hWeak.
  have hEqual := @euclidean_continuous_almost_equal R n
    (A_m (R_n R n) R^o m.+1) (@current_form_comass R h2 n m.+1)
    (@current_form_comass_real_norm R h2 n m.+1) U beta psi
    hBetaContinuous hPsiContinuous hAlmost.
  move=> x hx; rewrite -(@hEqual x hx).
  exact: (@hActual x hx).
- move=> hPointwise; apply: hIff.2.
  apply: (@measure_almost_everywhere_mono R (current_domain R n U)
    (@euclidean_open_domain_measure R n U)
    (proj1 (@euclidean_open_domain_measure_laws R n U hU)) setT _ _
    (measure_almost_everywhere_true
      (proj1 (@euclidean_open_domain_measure_laws R n U hU))))=> x _.
  exact: (exterior_derivative_unique
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@current_form_comass_real_norm R h2 n m)
    (@hActual (set_val x) (set_valP x))
    (@hPointwise (set_val x) (set_valP x))).
Qed.

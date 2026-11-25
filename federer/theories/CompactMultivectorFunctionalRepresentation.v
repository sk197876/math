(** Federer (1969), 4.1.19, p. 377: represent
    each restricted functional on Omega_m(U) by
    a bounded measurable differential form over
    the original U. Hahn–Banach preserves the
    original L1 bound, and restriction preserves
    every original field value and integral. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric ModuleQuotient
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading AlternatingPairing CurrentDomain
  CurrentCoefficientNorms MeasureUP PartialFunctionBasic MeasurableNormedFunctionUP
  MeasureIntegralUP SummableRealFunctionUP EuclideanOpenDomainMeasure
  CompactSummableFieldLaws CompactSummableMultivectors
  SummableFieldLaws CompactSummableFieldInclusion
  EuclideanOpenMultivectorLoneRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CompactRepresentation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation V := (exterior_power X m).
Local Notation Y := (A_m X R^o m).
Local Notation MN := (@current_vector_mass R h2 n m).
Local Notation hMN := (@current_vector_mass_real_norm R h2 n m).
Local Notation YN := (@current_form_comass R h2 n m).
Local Notation hYN := (@current_form_comass_real_norm R h2 n m).
Local Notation O := (@compact_summable_multivector_space R h2 n m U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n m U hU).
Local Notation size := (@compact_summable_multivector_size R h2 n m U hU).
Local Notation inclusion := (@compact_summable_field_inclusion R UT V MN hMN
  mu hMu).

(** Source for [compact_multivector_functional_representation]:
    the bounded form representing the original
    Omega_m functional in Federer 4.1.19,
    p. 377, has the same pointwise
    comass bound as that functional's original
    L1 estimate. Every original compactly supported
    raw field is retained on the same open U. *)
Theorem compact_multivector_functional_representation
    (beta : Hom O R^o) (c : R) :
  0 <= c -> (forall xi, `|beta xi| <= c*size xi) ->
  exists phi : UT -> Y,
    is_measurable_normed_function mu
      (partial_function_total (fun x => (phi x : real_norm_metric_space hYN))) /\
    (forall x, YN (phi x) <= c) /\
    forall xi : O, is_measure_integral mu
      (real_total_integrand (fun x => pairing (value xi x) (phi x)))
      (beta xi)%:E.
Proof.
move=> hC hBeta.
have [F [hAgree hBound]] := @compact_summable_bounded_functional_extension
  R UT V MN hMN mu hMu beta c hC hBeta.
have [phi [hPhi [hCap hAction]]] :=
  @euclidean_open_multivector_lone_representation R h2 n m U hU
    F c hC hBound.
exists phi; split; first exact: hPhi.
split; first exact: hCap.
move=> xi.
have hValue : @summable_field_value R UT V MN hMN mu hMu
    (inclusion xi) = value xi.
  rewrite /summable_field_value /compact_summable_multivector_value
    /compact_summable_field_value.
  by rewrite compact_summable_field_inclusion_evaluation.
have hIntegral := hAction (inclusion xi).
by rewrite hValue (hAgree xi) in hIntegral.
Qed.
End CompactRepresentation.

(** Federer (1969), 4.1.19, p. 377: bounded
    L1 functionals on the original multivector
    fields over U are represented by bounded
    measurable differential forms on that same U.
    Actual mass and comass retain their original
    natural degrees, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentVectorSpaces CurrentCovectorDual MeasureUP RadonMeasureUP
  CurrentDomainRadonSigmaFinite PartialFunctionBasic MeasurableNormedFunctionUP
  MeasureIntegralUP SummableRealFunctionUP EuclideanOpenDomainMeasure
  SummableFieldSealed SummableFieldLaws FiniteSummableDualRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section OpenMultivectorRepresentation.
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
Local Notation W := (@SummableField.space R UT V MN hMN mu hMu).
Local Notation value := (@summable_field_value R UT V MN hMN mu hMu).
Local Notation size := (@summable_field_size R UT V MN hMN mu hMu).

(** Source for [euclidean_open_multivector_lone_representation]:
    the actual bounded measurable m-form used in
    Federer 4.1.19, p. 377, represents
    the full L1 functional with pointwise
    comass at most its original bound. The
    original open U, original Lebesgue measure
    and every original raw field are retained;
    no ambient zero extension or volume restriction is added. *)
Theorem euclidean_open_multivector_lone_representation (F : Hom W R^o) (c : R) :
  0 <= c -> (forall w, `|F w| <= c*size w) ->
  exists phi : UT -> Y,
    is_measurable_normed_function mu
      (partial_function_total (fun x => (phi x : real_norm_metric_space hYN))) /\
    (forall x, YN (phi x) <= c) /\
    forall w : W, is_measure_integral mu
      (real_total_integrand (fun x => pairing (value w x) (phi x))) (F w)%:E.
Proof.
move=> hC hBound.
have hMeasure := @euclidean_open_domain_measure_laws R n U hU.
have hCountable := @current_domain_radon_countably_measurable R n U hU mu
  hMu hMeasure.2.
have [d [e he]] := @current_vector_finite_basis R h2 n m.
have [phi [hPhi [hPhiBound hAction]]] :=
  @finite_summable_dual_representation R UT V Y MN hMN
    (@current_covector_evaluation R n m) YN hYN
    (@current_covector_continuous_dual R h2 n m) d e he
    mu hMu hMeasure.2 hCountable F c hC hBound.
exists phi; split; first exact: hPhi.
split; first exact: hPhiBound.
move=> w; exact: hAction.
Qed.
End OpenMultivectorRepresentation.

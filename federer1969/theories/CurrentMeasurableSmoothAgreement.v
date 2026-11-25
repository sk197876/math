(** Federer (1969), 4.1.7, pp. 355–356:
    the locally summable measurable products
    extend the actual original smooth operations.
    Compare every original test action, using
    the same variation representation of T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import ScalarCoefficients Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingProduct AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentVectorSpaces
  CurrentEvaluation CurrentIntegrationCriterion NormalisedCurrentSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP MultivectorDualSealed
  CurrentMeasurableMultiplierUP CurrentMeasurableProductCoefficients CurrentMeasurableProducts
  SmoothRadonFieldLocalIntegral SmoothFunctionSpaceUP CurrentContraction CurrentVectorProduct
  CurrentTestFormProduct CurrentTestVectorInterior CurrentVectorFormInterior
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMeasurableSmoothAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation VE := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation represented := (fun m=>@is_integration_representable_current R h2 n m U hU).

(** Source for [current_smooth_form_variation_summable]:
    every original smooth form is locally
    ||T||-summable, supporting the extension in
    Federer 4.1.7, pp. 355–356. *)
Lemma current_smooth_form_variation_summable (T:C (k+p)) (hT:represented (k+p) T) (phi:E k):
  is_locally_summable_current_field (@current_form_comass_real_norm R h2 n k)
    (@NormalisedCurrent.measure R h2 n (k+p) U hU T hT) (fun x:UT=>ev k phi (set_val x)).
Proof.
have hBase:=normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n (k+p) U hU T hT).
exact:(@smooth_radon_field_locally_summable R X (Y k) NX (@current_form_comass R h2 n k)
  hNX (@current_form_comass_real_norm R h2 n k) U (E k) (ev k) (hE k)
  (@NormalisedCurrent.measure R h2 n (k+p) U hU T hT)
  (distribution_representation_measure hBase) (distribution_representation_radon hBase) phi).
Qed.

(** Source for [current_measurable_contraction_smooth_agreement]:
    the measurable contraction equals the original
    smooth contraction for every smooth form,
    Federer 4.1.7, pp. 355–356. *)
Theorem current_measurable_contraction_smooth_agreement (T:C (k+p)) hT (phi:E k):
  @current_measurable_contraction R h2 n k p U hU T hT
    (fun x:UT=>ev k phi (set_val x)) (current_smooth_form_variation_summable hT phi)=
  @current_contraction R h2 n k p U hU phi T.
Proof.
apply:(@current_values_extensional R h2 n p U hU)=>psi.
have hNew:=@current_measurable_contraction_action R h2 n k p U hU T hT
  (fun x:UT=>ev k phi (set_val x)) (current_smooth_form_variation_summable hT phi) psi.
have hBase:=normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n (k+p) U hU T hT).
have hOld:=distribution_representation_action hBase
  (@current_test_form_product R h2 n k p U hU phi psi).
have hPoint:(fun x:UT=>@MultivectorDual.evaluation R X (k+p)
    (@NormalisedCurrent.auxiliary_density R h2 n (k+p) U hU T hT x)
    (@current_test_value R h2 n U hU (k+p)
      (@current_test_form_product R h2 n k p U hU phi psi) (set_val x)))=
  (fun x:UT=>pairing (@NormalisedCurrent.auxiliary_density R h2 n (k+p) U hU T hT x)
    (form_wedge h2 (scalar_bilinear R) (ev k phi (set_val x))
      (@current_test_value R h2 n U hU p psi (set_val x)))).
  apply:funext=>x;rewrite MultivectorDual.laws
    (@current_test_form_product_values R h2 n k p U hU phi psi (set_val x) (set_valP x));by [].
rewrite hPoint in hOld.
rewrite current_contraction_evaluation.
exact:(congr1 (@fine R) (measure_integral_unique hNew hOld)).
Qed.

(** Source for [current_smooth_vector_variation_summable]:
    every original smooth multivector field is
    locally ||T||-summable, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma current_smooth_vector_variation_summable (T:C p) (hT:represented p T) (xi:VE k):
  is_locally_summable_current_field (@current_vector_mass_real_norm R h2 n k)
    (@NormalisedCurrent.measure R h2 n p U hU T hT) (fun x:UT=>vv k xi (set_val x)).
Proof.
have hBase:=normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n p U hU T hT).
exact:(@smooth_radon_field_locally_summable R X (Z k) NX (@current_vector_mass R h2 n k)
  hNX (@current_vector_mass_real_norm R h2 n k) U (VE k) (vv k) (hV k)
  (@NormalisedCurrent.measure R h2 n p U hU T hT)
  (distribution_representation_measure hBase) (distribution_representation_radon hBase) xi).
Qed.

(** Source for [current_measurable_vector_product_smooth_agreement]:
    the measurable product equals the original
    smooth vector product for every smooth
    multivector field, Federer 4.1.7, pp. 355–356. *)
Theorem current_measurable_vector_product_smooth_agreement (T:C p) hT (xi:VE k):
  @current_measurable_vector_product R h2 n k p U hU T hT
    (fun x:UT=>vv k xi (set_val x)) (current_smooth_vector_variation_summable hT xi)=
  @current_vector_product R h2 n k p U hU xi T.
Proof.
apply:(@current_values_extensional R h2 n (k+p) U hU)=>psi.
have hNew:=@current_measurable_vector_product_action R h2 n k p U hU T hT
  (fun x:UT=>vv k xi (set_val x)) (current_smooth_vector_variation_summable hT xi) psi.
have hBase:=normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n p U hU T hT).
have hOld:=distribution_representation_action hBase
  (@current_test_vector_interior R h2 n k p U hU xi psi).
have hPoint:(fun x:UT=>@MultivectorDual.evaluation R X p
    (@NormalisedCurrent.auxiliary_density R h2 n p U hU T hT x)
    (@current_test_value R h2 n U hU p
      (@current_test_vector_interior R h2 n k p U hU xi psi) (set_val x)))=
  (fun x:UT=>pairing (@NormalisedCurrent.auxiliary_density R h2 n p U hU T hT x)
    (current_vector_form_interior (vv k xi (set_val x))
      (@current_test_value R h2 n U hU (k+p) psi (set_val x)))).
  apply:funext=>x;rewrite MultivectorDual.laws
    (@current_test_vector_interior_values R h2 n k p U hU xi psi (set_val x) (set_valP x));by [].
rewrite hPoint in hOld.
rewrite current_vector_product_evaluation.
exact:(congr1 (@fine R) (measure_integral_unique hNew hOld)).
Qed.
End CurrentMeasurableSmoothAgreement.

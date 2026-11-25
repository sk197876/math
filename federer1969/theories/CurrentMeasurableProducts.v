(** Federer (1969), 4.1.7, pp. 355–356:
    the original contraction and vector product
    extend to every locally variation-summable
    measurable coefficient field. The values use
    the opaque multiplier interface and its
    independently specified integral action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import ScalarCoefficients Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingProduct AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentVectorSpaces CurrentVectorFormInterior CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMeasurableProductCoefficients CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierSealed
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMeasurableProducts.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation Z := (fun m=>exterior_power X m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation represented := (fun m=>@is_integration_representable_current R h2 n m U hU).
Local Notation mu := (fun m T hT=>@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta := (fun m T hT=>@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation F := (@current_density_form_contraction R h2 n k p).
Local Notation G := (@current_density_vector_product R n k p).

(** Source for [current_measurable_contraction]: the
    original T contracted with a measurable
    locally ||T||-summable k-form, Federer
    4.1.7, pp. 355–356. *)
Definition current_measurable_contraction (T:C (k+p)) (hT:represented (k+p) T)
    (phi:UT->Y k)
    (hPhi:is_locally_summable_current_field (@current_form_comass_real_norm R h2 n k)
      (mu (k+p) T hT) phi):C p:=
  @CurrentMeasurableMultiplier.value R h2 n (k+p) p U hU (Y k)
    (@current_form_comass R h2 n k) (@current_form_comass_real_norm R h2 n k)
    (@current_form_separable R h2 n k) F
    (@current_density_form_contraction_bounded R h2 n k p) T hT phi hPhi.

(** Source for [current_measurable_contraction_laws]:
    the contraction is represented by integration
    and has the original left-interior action,
    Federer 4.1.7, pp. 355–356. *)
Theorem current_measurable_contraction_laws (T:C (k+p)) hT phi hPhi:
  @is_current_measurable_multiplier R h2 n (k+p) p U hU (Y k) F T hT phi
    (@current_measurable_contraction T hT phi hPhi) /\
  represented p (@current_measurable_contraction T hT phi hPhi).
Proof. exact:CurrentMeasurableMultiplier.laws. Qed.

(** Source for [current_measurable_contraction_action]:
    the contraction integrates the original
    phi wedge psi pairing for every original
    test psi, Federer 4.1.7, pp. 355–356.
    The measurable phi need not be a test. *)
Theorem current_measurable_contraction_action (T:C (k+p)) hT phi hPhi psi:
  is_measure_integral (mu (k+p) T hT) (real_total_integrand
    (fun x=>pairing (eta (k+p) T hT x)
      (form_wedge h2 (scalar_bilinear R) (phi x)
        (@current_test_value R h2 n U hU p psi (set_val x)))))
    (@current_value R h2 n U hU p (@current_measurable_contraction T hT phi hPhi) psi)%:E.
Proof.
have h:=(@current_measurable_contraction_laws T hT phi hPhi).1 psi.
have hPoint:(fun x=>pairing (F (eta (k+p) T hT x) (phi x))
    (@current_test_value R h2 n U hU p psi (set_val x)))=
  (fun x=>pairing (eta (k+p) T hT x) (form_wedge h2 (scalar_bilinear R) (phi x)
    (@current_test_value R h2 n U hU p psi (set_val x)))).
  apply:funext=>x;exact:current_density_form_contraction_pairing.
by rewrite hPoint in h.
Qed.

(** Source for [current_measurable_vector_product]:
    the original T wedge xi for every
    measurable locally ||T||-summable k-vector
    field, Federer 4.1.7, pp. 355–356. *)
Definition current_measurable_vector_product (T:C p) (hT:represented p T)
    (xi:UT->Z k)
    (hXi:is_locally_summable_current_field (@current_vector_mass_real_norm R h2 n k)
      (mu p T hT) xi):C (k+p):=
  @CurrentMeasurableMultiplier.value R h2 n p (k+p) U hU (Z k)
    (@current_vector_mass R h2 n k) (@current_vector_mass_real_norm R h2 n k)
    (@current_vector_coefficient_separable R h2 n k) G
    (@current_density_vector_product_bounded R h2 n k p) T hT xi hXi.

(** Source for [current_measurable_vector_product_laws]:
    the product is integration-representable and
    has the original coefficient-product action,
    Federer 4.1.7, pp. 355–356. *)
Theorem current_measurable_vector_product_laws (T:C p) hT xi hXi:
  @is_current_measurable_multiplier R h2 n p (k+p) U hU (Z k) G T hT xi
    (@current_measurable_vector_product T hT xi hXi) /\
  represented (k+p) (@current_measurable_vector_product T hT xi hXi).
Proof. exact:CurrentMeasurableMultiplier.laws. Qed.

(** Source for [current_measurable_vector_product_action]:
    the product integrates precisely the original
    right-interior pairing, Federer 4.1.7,
    pp. 355–356. Its density has eta on
    the left and xi on the right. *)
Theorem current_measurable_vector_product_action (T:C p) hT xi hXi psi:
  is_measure_integral (mu p T hT) (real_total_integrand
    (fun x=>pairing (eta p T hT x)
      (current_vector_form_interior (xi x)
        (@current_test_value R h2 n U hU (k+p) psi (set_val x)))))
    (@current_value R h2 n U hU (k+p) (@current_measurable_vector_product T hT xi hXi) psi)%:E.
Proof.
have h:=(@current_measurable_vector_product_laws T hT xi hXi).1 psi.
have hPoint:(fun x=>pairing (G (eta p T hT x) (xi x))
    (@current_test_value R h2 n U hU (k+p) psi (set_val x)))=
  (fun x=>pairing (eta p T hT x) (current_vector_form_interior (xi x)
    (@current_test_value R h2 n U hU (k+p) psi (set_val x)))).
  apply:funext=>x;exact:current_density_vector_product_pairing.
by rewrite hPoint in h.
Qed.
End CurrentMeasurableProducts.

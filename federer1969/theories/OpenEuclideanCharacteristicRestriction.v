(** Federer (1969), 4.1.8, p. 362: viewing
    the original Euclidean characteristic current on
    a smaller original open domain preserves its
    literal subset integral. Use actual test zero extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation CurrentOpenRestriction
  OpenEuclideanCharacteristicCurrent EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [open_euclidean_characteristic_restriction]: the actual
    original open restriction of the Euclidean
    characteristic current on V is the same
    characteristic current viewed on U, supporting
    Federer 4.1.8, p. 362. No boundedness or
    containment of the measurable characteristic set is added. *)
Theorem open_euclidean_characteristic_restriction (R:realType) (h2:(1+1:R)!=0) n
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V x)
    (hUV:forall x,U x->V x)
    (B:set (R_n R n)) (hB:measure_measurable (@euclidean_lebesgue_measure R n) B):
  @current_open_restriction R h2 n n U V hU hV hUV
    (@open_euclidean_characteristic_current R h2 n V hV B hB)=
    @open_euclidean_characteristic_current R h2 n U hU B hB.
Proof.
apply:(@current_values_extensional R h2 n n U hU)=>phi.
rewrite current_open_restriction_evaluation.
pose P:=@current_open_test_extension R h2 n n U V hU hV hUV.
have hVIntegral:=@open_euclidean_characteristic_current_action R h2 n V hV B hB (P phi).
have hUIntegral:=@open_euclidean_characteristic_current_action R h2 n U hU B hB phi.
have hFunction:(fun x=>pairing (e_lambda (@coordinate_basis R n) (ord_tuple n))
    (@current_test_value R h2 n V hV n (P phi) x))=
    (fun x=>pairing (e_lambda (@coordinate_basis R n) (ord_tuple n))
      (@current_test_value R h2 n U hU n phi x)).
  apply:funext=>x;by rewrite current_open_test_extension_values.
rewrite hFunction in hVIntegral.
exact:EFin_inj (measure_integral_unique hVIntegral hUIntegral).
Qed.

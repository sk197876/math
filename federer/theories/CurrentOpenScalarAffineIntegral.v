(** Federer (1969), 4.1.8, p. 362: the actual
    scalar-test endpoint formula on every original open
    domain. Zero extension, already proved for the
    original tests, supplies the global smooth scalar
    function used in the affine fundamental theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingZero AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces CurrentTestExteriorDerivative
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentFullScalarAffineIntegral
  ConvexMetricSegment LebesgueScalarMeasure MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentOpenScalarAffineIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior NX A x.
Local Notation hInclusion := (fun (x:X) (_:A x)=>Logic.I).
Local Notation value := (@current_test_value R h2 n A hA 0%N).
Local Notation value1 := (@current_test_value R h2 n A hA 1%N).
Local Notation derivative := (@current_test_exterior_derivative R h2 n 0%N A hA).
Local Notation fullValue1 := (@current_test_value R h2 n (fun _=>True) hFull 1%N).
Local Notation fullDerivative := (@current_test_exterior_derivative R h2 n 0%N (fun _=>True) hFull).
Local Notation P := (fun k=>@current_open_test_extension R h2 n k A (fun _=>True) hA hFull hInclusion).

(** Source for [current_open_scalar_affine_integral]: the
    original scalar-test differential has its endpoint
    integral, supporting the segment boundary in Federer
    4.1.8, p. 362. The genuine smooth zero extension
    removes any assumption that the whole affine line
    remains in the original domain. *)
Theorem current_open_scalar_affine_integral psi (u v:X):
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>pairing (exterior_first_inclusion X (v-u))
      (value1 (derivative psi) (metric_segment_point u v t))))
    (zero_form_value (value psi v)-zero_form_value (value psi u))%:E.
Proof.
have hIntegral:=@current_full_scalar_affine_integral R h2 n (P 0%N psi) u v.
have hValues x:fullValue1 (fullDerivative (P 0%N psi)) x=value1 (derivative psi) x.
  rewrite -(@current_open_test_exterior_commutes R h2 n 0%N A (fun _=>True)
    hA hFull hInclusion psi).
  exact:current_open_test_extension_values.
have hIntegrand:(fun t=>pairing (exterior_first_inclusion X (v-u))
    (fullValue1 (fullDerivative (P 0%N psi)) (metric_segment_point u v t)))=
    (fun t=>pairing (exterior_first_inclusion X (v-u))
      (value1 (derivative psi) (metric_segment_point u v t))).
  apply:funext=>t;by rewrite hValues.
by rewrite hIntegrand !current_open_test_extension_values in hIntegral.
Qed.
End CurrentOpenScalarAffineIntegral.

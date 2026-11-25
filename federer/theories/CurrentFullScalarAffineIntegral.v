(** Federer (1969), 4.1.8, p. 362: integrate
    the actual scalar-test differential along the original
    affine segment. The original chain rule and interval
    fundamental theorem supply the endpoint formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormOpenDomainLaws NormClassOneUP NormClassOneDirectionalField NormDifferentialAffineLine
  NormHigherCurveDerivativeUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingZero AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces CurrentTestExteriorDerivative CurrentFullScalarTestDifferential
  ConvexMetricSegment LebesgueScalarMeasure RealClassOneSegmentIntegral
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFullScalarAffineIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation value := (@current_test_value R h2 n (fun _=>True) hFull 0%N).
Local Notation value1 := (@current_test_value R h2 n (fun _=>True) hFull 1%N).
Local Notation derivative := (@current_test_exterior_derivative R h2 n 0%N (fun _=>True) hFull).

(** Source for [current_full_scalar_affine_integral]: the
    integral of the original one-form differential along
    the affine segment is the scalar test's endpoint
    difference, supporting Federer 4.1.8, p. 362, by
    3.1.11, pp. 220–221. No nonzero velocity or
    positive ambient dimension is needed. *)
Theorem current_full_scalar_affine_integral psi (u v:X):
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>pairing (exterior_first_inclusion X (v-u))
      (value1 (derivative psi) (metric_segment_point u v t))))
    (zero_form_value (value psi v)-zero_form_value (value psi u))%:E.
Proof.
have[D [hClass hPair]]:=@current_full_scalar_test_differential R h2 n psi.
pose f x:=zero_form_value (value psi x).
pose F t:=f (u+t*:(v-u)).
pose G t:=D (u+t*:(v-u)) (v-u).
have hDerivative t:has_norm_differential NS NS (fun _=>True) F t
    (@scalar_coefficient_linear_map R R^o (G t)).
  have hPath:=@norm_differential_along_affine_line R X R^o NX NS hNX hNS
    (fun _=>True) f u (v-u) t (D (u+t*:(v-u)))
    (norm_class_one_differential hClass Logic.I).
  have hSame:hom_comp (D (u+t*:(v-u))) (@scalar_coefficient_linear_map R X (v-u))=
      @scalar_coefficient_linear_map R R^o (G t).
    apply:hom_ext=>s;rewrite hom_compE /scalar_coefficient_linear_map /= linearZ.
    by [].
  by rewrite hSame in hPath.
have hDirectional:=@norm_class_one_directional_continuous R X R^o NX NS hNX hNS
  (fun _=>True) f D (v-u) hClass.
have hContinuous:=@norm_class_zero_along_affine_line R X R^o NX NS hNX
  (fun _=>True) (fun x=>D x (v-u)) u (v-u) hDirectional.
have hIntegral:=@real_class_one_segment_integral R F G 0 1 ler01 hDerivative hContinuous.
have hIntegrand:(fun t=>pairing (exterior_first_inclusion X (v-u))
    (value1 (derivative psi) (metric_segment_point u v t)))=G.
  apply:funext=>t;exact:hPair.
rewrite hIntegrand.
have hOne:F 1=zero_form_value (value psi v).
  by rewrite /F /f -/(metric_segment_point u v 1) metric_segment_one.
have hZero:F 0=zero_form_value (value psi u).
  by rewrite /F /f -/(metric_segment_point u v 0) metric_segment_zero.
by rewrite hOne hZero in hIntegral.
Qed.
End CurrentFullScalarAffineIntegral.

(** Federer (1969), 4.1.7, p. 356: actual
    existence of currents with locally integrable
    multivector density. Reuse the original weak-dual
    field construction from 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentMultivectorDual MultivectorDualSealed MultivectorDualUP CurrentDensityAction
  MeasureUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestEvaluation DistributionIntegralFieldUP
  DistributionIntegralFunctionalContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDensityExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation hE := (@current_smooth_space_laws R h2 n (fun _=>True) hFull m).
Local Notation D := (@current_smooth_derivatives R h2 n (fun _=>True) hFull m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n (fun _=>True) hFull m).
Variable gamma:set X->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable gamma A.
Variable xi:X->V.
Hypothesis hField:@is_locally_integrable_weak_dual_field R X Y NX hNX V ed VN O hO gamma xi.

(** Source for [current_from_density_exists]: the
    original mass-integrable field produces an
    actual current, Federer 4.1.7, p. 356.
    In particular this applies to the printed
    Lebesgue-density currents. No hypothetical
    current action is assumed. *)
Theorem current_from_density_exists:
  exists T:@current_space R h2 n (fun _=>True) hFull m,
    is_current_density_action gamma xi T.
Proof.
have [T hAction]:=@distribution_from_dual_field_exists R X Y NX NY hNX hNY V ed VN hDual
  (@current_form_separable R h2 n m) O hO gamma hGamma hOpen xi
  (integrable_dual_field_weak_measurable hField) E ev hE D hD
  (integrable_dual_field_local_norm hField).
exists T=>psi.
have h:=hAction psi.
have hEq:(fun x=>ed (xi x) (smooth_test_value hE psi x))=
    (fun x=>pairing (xi x) (@current_test_value R h2 n (fun _=>True) hFull m psi x)).
  apply:funext=>x;exact:MultivectorDual.laws.
by rewrite hEq in h.
Qed.
End CurrentDensityExistence.

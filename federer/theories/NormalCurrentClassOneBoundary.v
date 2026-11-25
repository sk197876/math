(** Federer (1969), 4.1.7, p. 358:
    (boundary T)(phi)=T(d phi) for every
    normal current T of positive degree
    and every class-one form of the
    preceding degree on its original domain.
    The two values are the original
    unique L1 extensions of 4.1.5.
    Compact support of phi is not required. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormClassHigherDerivative InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms ExteriorDerivativeUP CurrentCoefficientNorms CurrentSpaces CurrentDomain
  CurrentBoundary CurrentBoundarySupport CurrentTestExteriorDerivative CurrentIntegrationCriterion
  NormalCurrentsUP NormalCurrentBoundary NormalisedCurrentSealed CurrentOriginalBallFormula
  CurrentClassOneExterior CurrentClassOneTestApproximation NormalCurrentClassOneMembership
  NormalCurrentLoneLimit CurrentLoneOriginalAgreement SmoothCompactSet SmoothTestEvaluation
  PartialFunctionBasic MeasureLpMembershipUP PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Theory.
Local Open Scope ring_scope.
Section NormalCurrentClassOneBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation hNZ := (@current_form_comass_real_norm R h2 n m.+1).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.+1.
Hypothesis hNormal:@is_normal_current R h2 n U hU m.+1 T.
Local Notation bd := (@current_boundary R h2 n m U hU T).
Local Notation hBoundaryNormal := (@normal_current_boundary R h2 n U hU m T hNormal).
Local Notation muT := (@NormalisedCurrent.measure R h2 n m.+1 U hU T hNormal.1.1).
Local Notation etaT := (@NormalisedCurrent.auxiliary_density R h2 n m.+1 U hU T hNormal.1.1).
Local Notation hT := (@NormalisedCurrent.laws R h2 n m.+1 U hU T hNormal.1.1).
Local Notation muB := (@NormalisedCurrent.measure R h2 n m U hU bd hBoundaryNormal.1.1).
Local Notation etaB := (@NormalisedCurrent.auxiliary_density R h2 n m U hU bd hBoundaryNormal.1.1).
Local Notation hB := (@NormalisedCurrent.laws R h2 n m U hU bd hBoundaryNormal.1.1).
Local Notation IT := (@current_representation_lone_integral R h2 n m.+1 U hU T muT etaT hT).
Local Notation IB := (@current_representation_lone_integral R h2 n m U hU bd muB etaB hB).
Let totalY (f:X->Y):=partial_function_total (fun x:UT=>(f (set_val x):real_norm_metric_space hNY)).
Let totalZ (f:X->Z):=partial_function_total (fun x:UT=>(f (set_val x):real_norm_metric_space hNZ)).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation next := (@current_test_value R h2 n U hU m.+1).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).

(** Source for [normal_current_class_one_boundary]:
    the original normal-current boundary formula
    for every original class-one form on U,
    Federer 4.1.7, p. 358. Both
    L1 membership assertions are proved;
    beta is the actual exterior derivative,
    and the original open domain is retained. *)
Theorem normal_current_class_one_boundary (phi:X->Y) (beta:X->Z):
  norm_class hNX hNY U phi 1%N->
  (forall x,U x->has_exterior_derivative NX NY U phi x (beta x))->
  is_measure_lp_function muB 1 (totalY phi) /\
  is_measure_lp_function muT 1 (totalZ beta) /\
  IB (totalY phi)=IT (totalZ beta).
Proof.
move=>hClass hBeta.
have hMember:=@normal_current_class_one_lone_membership R h2 n m U hU T hNormal
  phi beta hClass hBeta.
split;first exact:hMember.1.
split;first exact:hMember.2.
have [b [hContinuous hActual]]:=@current_class_one_exterior_continuous R h2 n m U phi hClass.
have hEqual x (hx:U x):b x=beta x.
  exact:(exterior_derivative_unique hNX hNY (hActual x hx) (hBeta x hx)).
have hBetaContinuous:=norm_class_zero_domain_agreement hEqual hContinuous.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m.+1 T) (fun x hx=>hx.1) hNormal.2.
have [P hApprox]:=@current_class_one_test_approximation R h2 n m U hU K phi beta hClass hBeta.
have hValueContinuous e:norm_class_zero NX NY U (value (P e)).
  exact:(norm_class_continuous (smooth_test_value_smooth
    (@current_smooth_space_laws R h2 n U hU m) (P e) 0%N)).
have hNextContinuous e:norm_class_zero NX NZ U (next (d (P e))).
  exact:(norm_class_continuous (smooth_test_value_smooth
    (@current_smooth_space_laws R h2 n U hU m.+1) (d (P e)) 0%N)).
have hLimitB:positive_norm_limit (fun t:R^o=>`|t|)
    (fun e=>IB (totalY (value (P e)))) (IB (totalY phi)).
  apply:(@normal_current_lone_limit_on_support R h2 n m U hU bd hBoundaryNormal
    1 phi (fun e=>value (P e)) ltr01 (norm_class_continuous hClass)
    (fun e _ _=>hValueContinuous e))=>epsilon hEpsilon.
  have [delta [hDelta hBound]]:=hApprox epsilon hEpsilon.
  exists delta;split=>// e he hed x hx.
  exact:(hBound e he hed x (@current_boundary_support_subset R h2 n m U hU T x hx)).1.
have hLimitT:positive_norm_limit (fun t:R^o=>`|t|)
    (fun e=>IT (totalZ (next (d (P e))))) (IT (totalZ beta)).
  apply:(@normal_current_lone_limit_on_support R h2 n m.+1 U hU T hNormal
    1 beta (fun e=>next (d (P e))) ltr01 hBetaContinuous
    (fun e _ _=>hNextContinuous e))=>epsilon hEpsilon.
  have [delta [hDelta hBound]]:=hApprox epsilon hEpsilon.
  exists delta;split=>// e he hed x hx;exact:(hBound e he hed x hx).2.
have hEvaluation e:IB (totalY (value (P e)))=IT (totalZ (next (d (P e)))).
  rewrite (@current_lone_extension_original R h2 n m U hU bd muB etaB hB (P e))
    (@current_lone_extension_original R h2 n m.+1 U hU T muT etaT hT (d (P e))).
  exact:current_boundary_evaluation.
have hSameLimit:positive_norm_limit (fun t:R^o=>`|t|)
    (fun e=>IB (totalY (value (P e)))) (IT (totalZ beta)).
  apply:(positive_norm_limit_eventual_equality _ hLimitT).
  exists 1;split;first exact:ltr01.
  move=>e _ _;exact:esym (hEvaluation e).
exact:(positive_norm_limit_unique (@scalar_absolute_value_norm R) hLimitB hSameLimit).
Qed.
End NormalCurrentClassOneBoundary.

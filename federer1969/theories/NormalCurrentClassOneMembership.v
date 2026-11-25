(** Federer (1969), 4.1.7, p. 358:
    every original class-one form and
    its actual exterior derivative belong to
    the two variation L1 spaces in
    the normal-current boundary formula. The
    form retains its original domain and
    need not have compact support. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentDomain CurrentBoundary NormalCurrentsUP
  NormalCurrentBoundary CurrentIntegrationCriterion NormalisedCurrentSealed CurrentClassOneExterior
  NormalCurrentContinuousLoneMember ExteriorDerivativeUP PartialFunctionBasic MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section NormalCurrentClassOneMembership.
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
Local Notation muB := (@NormalisedCurrent.measure R h2 n m U hU bd hBoundaryNormal.1.1).

(** Source for [normal_current_class_one_lone_membership]:
    phi is in L1(||boundary T||)
    and d phi is in L1(||T||),
    supporting the unrestricted class-one boundary
    identity of Federer 4.1.7, p. 358.
    The supplied beta has the actual
    original exterior derivative graph on U. *)
Theorem normal_current_class_one_lone_membership (phi:X->Y) (beta:X->Z):
  norm_class hNX hNY U phi 1%N->
  (forall x,U x->has_exterior_derivative NX NY U phi x (beta x))->
  is_measure_lp_function muB 1 (partial_function_total
    (fun x:UT=>(phi (set_val x):real_norm_metric_space hNY))) /\
  is_measure_lp_function muT 1 (partial_function_total
    (fun x:UT=>(beta (set_val x):real_norm_metric_space hNZ))).
Proof.
move=>hClass hBeta;split.
- exact:(@normal_current_continuous_lone_member R h2 n m U hU bd hBoundaryNormal
    phi (norm_class_continuous hClass)).
- have [b [hContinuous hActual]]:=@current_class_one_exterior_continuous R h2 n m U phi hClass.
  have hEqual x (hx:U x):b x=beta x.
    exact:(exterior_derivative_unique hNX hNY (hActual x hx) (hBeta x hx)).
  have hClassB:=(@norm_class_zeroP R X Z NX NZ hNX hNZ U b).2 hContinuous.
  have hClassBeta:=@norm_class_domain_agreement R X Z NX NZ hNX hNZ U b beta 0%N hEqual hClassB.
  exact:(@normal_current_continuous_lone_member R h2 n m.+1 U hU T hNormal beta
    ((@norm_class_zeroP R X Z NX NZ hNX hNZ U beta).1 hClassBeta)).
Qed.
End NormalCurrentClassOneMembership.

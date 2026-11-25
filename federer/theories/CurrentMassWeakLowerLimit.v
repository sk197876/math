(** Federer (1969), 4.1.5, p. 350, used in
    4.1.12, pp. 368–369: original mass is lower
    semicontinuous under convergence on every test.
    This adapter applies the preceding scalar-gauge
    theorem to the already identified current mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain CurrentMassSealed CurrentMassBasic
  DistributionVariationLowerLimit ExtendedLowerLimitUP ExtendedLowerLimit ExtendedLowerLimitUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMassWeakLowerLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := [the choiceType of set_type (U:set (real_norm_metric_space hNX))].
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_mass_weak_lower_limit]:
    M(T)<=liminf M(T_k) under original testwise
    convergence, supporting the two series in Federer
    4.1.12, pp. 368–369, by the scalar-gauge
    lower-limit assertion of 4.1.5, p. 350.
    Infinite masses require no representation premise. *)
Theorem current_mass_weak_lower_limit (P:nat->C) (T:C):
  (forall phi:DT,forall epsilon:R,0<epsilon->exists N,forall k,(N<=k)%N->
    `|action (P k) phi-action T phi|<epsilon)->
  (M T<=extended_lower_limit (fun k=>M (P k)))%E.
Proof.
move=>hWeak.
exact:(@distribution_variation_lower_limit R UT Y NY DT dvalues
  (fun k=>action (P k)) (action T) (fun _=>1) (fun k=>M (P k)) (M T)
  (fun k=>@current_mass_majorant_one R h2 n m U hU (P k))
  (@current_mass_majorant_one R h2 n m U hU T) hWeak).
Qed.

(** Source for [current_mass_weak_closed_bound]:
    an eventual original mass bound survives testwise
    convergence, supporting mass tails and mass closure
    in Federer 4.1.12, pp. 368–369. This is
    the preceding liminf theorem and its proved
    eventual-upper-bound law, without a new limit argument. *)
Corollary current_mass_weak_closed_bound (P:nat->C) (T:C) b N:
  (forall phi:DT,forall epsilon:R,0<epsilon->exists k,forall M,(k<=M)%N->
    `|action (P M) phi-action T phi|<epsilon)->
  (forall k,(N<=k)%N->(M (P k)<=b)%E)->(M T<=b)%E.
Proof.
move=>hWeak hMass.
have hLower:=@current_mass_weak_lower_limit P T hWeak.
have hUpper:=@extended_lower_limit_eventual_upper_bound R (fun k=>M (P k))
  (extended_lower_limit (fun k=>M (P k))) b (extended_lower_limit_laws _) (ex_intro _ N hMass).
exact:le_trans hLower hUpper.
Qed.
End CurrentMassWeakLowerLimit.

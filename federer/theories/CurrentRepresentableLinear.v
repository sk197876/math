(** Federer (1969), 4.1.7, p. 358: closure
    of represented currents under linear combinations.
    Reuse the exact finite-gauge criterion of
    4.1.5 instead of constructing new measures
    for sums of currents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionFiniteVariationUP FiniteDistributionVariationLinear CurrentIntegrationCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentRepresentableLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation represented := (@is_integration_representable_current R h2 n m U hU).

(** Source for [represented_current_zero]: the zero
    current is representable by integration,
    supporting Federer 4.1.7, p. 358. *)
Theorem represented_current_zero:represented (0:C).
Proof.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU (0:C)).1.
change (@is_finite_distribution_variation R XT U Y NY DT values (action (0:C))).
rewrite (linear0 action).
exact:(@finite_distribution_variation_zero R XT U Y NY hNY DT values).
Qed.

(** Source for [represented_current_linear]: each
    real linear combination is representable by
    integration, supporting the vector-space assertion
    in Federer 4.1.7, p. 358. *)
Theorem represented_current_linear c (T S:C):
  represented T->represented S->represented (c*:T+S).
Proof.
move=>hT hS.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU (c*:T+S)).1.
change (@is_finite_distribution_variation R XT U Y NY DT values (action (c*:T+S))).
rewrite (linearP action).
exact:(@finite_distribution_variation_linear R XT U Y NY hNY DT values c (action T) (action S)
  ((@current_integration_finite_gauge_criterion R h2 n m U hU T).2 hT)
  ((@current_integration_finite_gauge_criterion R h2 n m U hU S).2 hS)).
Qed.

(** Source for [represented_current_difference]: the
    difference of two represented currents is
    representable, supporting the scalar boundary
    and normality arguments in Federer 4.1.7,
    pp. 356–358. *)
Theorem represented_current_difference (T S:C):
  represented T->represented S->represented (T-S).
Proof.
move=>hT hS.
have h:=@represented_current_linear (-1) S T hS hT.
by rewrite scaleN1r addrC in h.
Qed.
End CurrentRepresentableLinear.

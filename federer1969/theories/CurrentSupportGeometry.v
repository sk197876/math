(** Federer (1969), 4.1.7, pp. 355–359:
    original current supports and their compact
    constraints. Reuse the actual test-annihilation
    criterion from 4.1.1, pp. 344–345,
    including its relative-domain convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms
  CurrentSpaces SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  FunctionalSupportUP SmoothTestSupportCriterion SmoothFunctionalSupportBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSupportGeometry.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [current_test_support]: the original
    support of a compact test form,
    supporting Federer 4.1.7, pp. 355–359. *)
Definition current_test_support (phi:DT):set X:=
  @smooth_function_support R X Y NX hNX U DT value phi.

(** Source for [current_support_compact_criterion]:
    support containment in a compact K is
    exactly annihilation of all original tests
    supported in U minus K, supporting
    Federer 4.1.7, pp. 355–359. *)
Theorem current_support_compact_criterion (K:smooth_compact_set hNX U) (T:C):
  (support T `<=` smooth_compact_carrier K)<->
    forall phi:DT,current_test_support phi `<=` (U `&` ~` smooth_compact_carrier K)->action T phi=0.
Proof.
exact:(@smooth_test_support_compact_criterion R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K (action T)).
Qed.

(** Source for [current_support_compact_bound]:
    an original current supported in a compact
    K has compact support in U,
    supporting Federer 4.1.7, p. 358. *)
Theorem current_support_compact_bound (K:smooth_compact_set hNX U) (T:C):
  support T `<=` smooth_compact_carrier K->compact [set x:real_norm_metric_space hNX|support T x].
Proof.
exact:(@smooth_functional_support_compact R X Y NX hNX U DT value K (action T)).
Qed.

(** Source for [current_support_zero_subset]: the
    zero current satisfies every original compact
    support constraint, supporting Federer 4.1.7,
    p. 358. *)
Theorem current_support_zero_subset (K:smooth_compact_set hNX U):
  support (0:C) `<=` smooth_compact_carrier K.
Proof.
apply:(current_support_compact_criterion K (0:C)).2=>phi _.
by rewrite (linear0 action) hom_zeroE.
Qed.

(** Source for [current_support_linear_subset]: every
    real linear combination preserves a common
    compact support constraint, supporting N_(m,K)
    in Federer 4.1.7, p. 358. *)
Theorem current_support_linear_subset (K:smooth_compact_set hNX U) c (T S:C):
  support T `<=` smooth_compact_carrier K->support S `<=` smooth_compact_carrier K->
  support (c*:T+S) `<=` smooth_compact_carrier K.
Proof.
move=>hT hS;apply:(current_support_compact_criterion K (c*:T+S)).2=>phi hPhi.
have hT0:=(current_support_compact_criterion K T).1 hT phi hPhi.
have hS0:=(current_support_compact_criterion K S).1 hS phi hPhi.
by rewrite (linearP action) hom_addE hom_scaleE hT0 hS0 scaler0 addr0.
Qed.
End CurrentSupportGeometry.

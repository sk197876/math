(** Federer (1969), 4.1.8, p. 360: detect
    support points by original compact tests with nonzero
    action, using the actual local-annihilation definition
    from 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormOpenTopology NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms
  CurrentSpaces SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  FunctionalSupportUP CurrentSupportGeometry SmoothTestSupportCriterion SmoothFunctionalSupportBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSupportLocalTest.
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

(** Source for [current_support_local_nonzero_test]: every
    open neighbourhood of a point in the original current
    support contains the support of a test with nonzero
    current action, supporting Federer 4.1.8, p. 360,
    by the definition in 4.1.1, p. 344. *)
Theorem current_support_local_nonzero_test (T:C) x (W:set X):
  support T x->norm_open_family hNX W->W x->
  exists phi:DT,@current_test_support R h2 n m U hU phi `<=` W /\ action T phi<>0.
Proof.
move=>hPoint hW hWx;apply:contrapT=>hNone.
apply:hPoint.2;exists W;split;last exact:hWx.
split;first exact:hW.
move=>phi hPhi;apply:contrapT=>hNonzero.
apply:hNone;by exists phi.
Qed.
End CurrentSupportLocalTest.

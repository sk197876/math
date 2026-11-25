(** Federer (1969), 4.1.1, pp. 344–345: support
    containment is characterized by vanishing on tests
    supported off the prescribed compact set. The proof
    uses the preceding actual partition support theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  FunctionalSupportUP SmoothTestFunctionalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestSupportCriterion.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U DT value).

(** Source for [smooth_test_support_compact_criterion]:
    spt T lies in K exactly when T annihilates all
    tests supported in U minus K, supporting the fixed-
    support weak dual spaces in Federer 4.1.1,
    pp. 344–345. *)
Theorem smooth_test_support_compact_criterion (K:smooth_compact_set hNX U) (T:Hom DT R^o):
  (tsupport T `<=` smooth_compact_carrier K) <->
  forall f,support f `<=` (U `&` ~` smooth_compact_carrier K) ->T f=0.
Proof.
split.
- move=>hK f hf.
  apply:(@smooth_test_functional_disjoint_support_zero R X Y NX NY hNX hNY n b hb U hU E ev hE T f)=>x ht hp.
  exact:(hf x hp).2 (hK x ht).
- move=>hT x [hx hSupp].
  case:(pselect (smooth_compact_carrier K x))=>// hNo.
  apply:False_ind; apply:hSupp.
  pose W:=U `&` ~` smooth_compact_carrier K.
  have hOpenU:@open XN U.
    rewrite openE=>y hy.
    exact ((@norm_domain_interior_neighbourhood R X NX hNX U y).1 (@hU y hy)).
  have hClosed:=compact_closed (@metric_hausdorff R XN) (smooth_compact_is_compact K).
  exists W; split; last by split.
  split; first exact:openI hOpenU (closed_openC hClosed).
  exact hT.
Qed.
End TestSupportCriterion.

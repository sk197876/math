(** Federer (1969), 4.1.1, p. 344: a
    smooth-dual support point outside K supplies an
    actual compactly supported test outside K on
    which the functional is nonzero. This is the
    local selection used in the common-support proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  ContinuousMultilinearSealed OpenFamilyTopologyUP NormOpenTopology SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  FunctionalSupportUP SmoothDualRestriction SmoothCutoffReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualEscapingTest.
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
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U E ev).

(** Source for [smooth_dual_escaping_compact_test]: failure
    of support containment in K is witnessed by a
    compact test supported in U minus K with
    nonzero functional value, supporting Federer
    4.1.1, p. 344. No extra order or
    derivative bound is imposed on the witness. *)
Theorem smooth_dual_escaping_compact_test (L:Hom E R^o) (K:smooth_compact_set hNX U):
  open_family_continuous (smooth_function_opens hD) (norm_open_family (@scalar_absolute_value_norm R)) L ->
  ~(tsupport L `<=` smooth_compact_carrier K) ->
  exists f:DT,(@smooth_function_support R X Y NX hNX U DT value f `<=`
    (U `&` ~` smooth_compact_carrier K)) /\ L (inc f)<>0.
Proof.
move=>hL hEsc.
have hSome:exists x,tsupport L x /\ ~smooth_compact_carrier K x.
  case:(pselect (exists x,tsupport L x /\ ~smooth_compact_carrier K x))=>// hNone.
  apply:False_ind; apply:hEsc=>x hx.
  case:(pselect (smooth_compact_carrier K x))=>// hn.
  exact:False_ind _ (hNone (ex_intro _ x (conj hx hn))).
have [x [hx hNo]]:=hSome.
pose W:=U `&` ~` smooth_compact_carrier K.
have hOpenU:@open (real_norm_metric_space hNX) U.
  rewrite openE=>y hy.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U y).1 (@hU y hy)).
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K).
have hW:@open (real_norm_metric_space hNX) W:=openI hOpenU (closed_openC hClosed).
have hWitness:exists a:E,support a `<=` W /\ L a<>0.
  case:(pselect (exists a:E,support a `<=` W /\ L a<>0))=>// hNone.
  apply:False_ind; apply:hx.2; exists W; split; last by split; [exact:hx.1|exact hNo].
  split; first exact hW.
  move=>a ha; case:(pselect (L a=0))=>// hn.
  exact:False_ind _ (hNone (ex_intro _ a (conj ha hn))).
have [a [ha hLa]]:=hWitness.
have [C hAgree]:=@continuous_smooth_functional_cutoff_agreement R X Y NX NY hNX hNY U E ev hE
  D hD n b hb hU L hL.
pose f:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE C a.
exists f; split.
- move=>y hy; apply:ha.
  exact:(@smooth_cutoff_replacement_support_subset R X Y NX NY hNX hNY n b hb U hU E ev hE C a y hy).
- by rewrite (hAgree a).
Qed.
End SmoothDualEscapingTest.

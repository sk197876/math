(** Federer (1969), 4.1.1, p. 345: a compactly
    supported test equals the finite sum of its products
    with all active partition terms. This is an exact
    function identity before any functional is applied. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothCompactPartitionUP FiniteFamilySumUP SmoothMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteTestDecomposition.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Variable J:choiceType.
Variable I:set J.
Variable v:J->X->R.
Hypothesis hv:is_smooth_compact_partition hNX U I v.
Variable K:smooth_compact_set hNX U.
Variable F:{fset J}.
Hypothesis hFI:forall s,s \in F ->I s.
Hypothesis hInactive:forall x,smooth_compact_carrier K x ->forall s,I s ->s \notin F ->v s x=0.
Variable P:forall s:F,Hom DT DT.
Hypothesis hP:forall s:F,is_smooth_multiplier U value (v (val s)) (P s).

(** Source for [smooth_test_finite_partition_identity]: phi
    is the sum of v_s phi over one finite active set,
    supporting T=sum T L v_s in Federer 4.1.1,
    p. 345. No convergence assumption replaces this identity. *)
Theorem smooth_test_finite_partition_identity f:
  @smooth_function_support R X Y NX hNX U DT value f `<=` smooth_compact_carrier K ->
  \sum_(s:F) P s f=f.
Proof.
move=>hSupp; apply:(smooth_test_values_extensional hE)=>x hx.
have hLinear:linear (fun g:DT=>value g x).
  move=>c g h.
  exact:(congr1 (fun q:X->Y=>q x) (@smooth_test_values_linear R X Y NX NY hNX hNY U E ev hE c g h)).
pose Lx:=@HomMap R DT Y (fun g=>value g x) (introT (asboolP _) hLinear).
have hEval:value (\sum_(s:F) P s f) x=\sum_(s:F) value (P s f) x.
  change (Lx (\sum_(s:F) P s f)=\sum_(s:F) Lx (P s f)).
  by rewrite linear_sum.
rewrite hEval.
have hProduct:(\sum_(s:F) value (P s f) x)=\sum_(s:F) v (val s) x*:value f x.
  apply:eq_bigr=>s _; exact:(hP s f hx).
rewrite hProduct -scaler_suml.
case:(pselect (smooth_compact_carrier K x))=>[hKx|hKx].
- have hOne:=smooth_partition_sum_one hv hx hFI (@hInactive x hKx).
  rewrite big_seq_fsetE in hOne; by rewrite -hOne scale1r.
- have hZero:value f x=0.
    case:(pselect (value f x=0))=>// hne.
    apply:False_ind; apply:hKx; apply:hSupp; split=>//.
    exact:(@subset_closure (NormMetric.real_norm_metric_space hNX) _ x hne).
  by rewrite hZero scaler0.
Qed.
End FiniteTestDecomposition.

(** Federer (1969), 4.1.1, p. 345: a distribution
    is the weak limit of its partition restrictions along
    every increasing finite exhaustion. On each actual
    compactly supported test, the evaluations are eventually
    exactly equal, by the original finite partition identity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import Hom Biorthogonal RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  ContinuousMultilinearSealed OpenFamilyTopologyUP OpenFamilyConvergence NormOpenTopology
  WeakEvaluationConvergenceUP WeakEvaluationTopologySealed SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothCompactPartitionUP
  SmoothPartitionCompactSelection SmoothMultiplierUP SmoothTestScalarMultiplier SmoothTestFiniteDecomposition
  ContinuousRealDual DistributionScalarRestriction CountableFiniteExhaustionUP FiniteExhaustionCapturesFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionPartition.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
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
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Variable J:choiceType.
Variable I:set J.
Variable v:J->X->R.
Hypothesis hv:is_smooth_compact_partition hNX U I v.
Variable C:nat->{fset J}.
Hypothesis hC:is_countable_finite_exhaustion I C.

(** Source for [distribution_partition_weight_class]: each
    actual partition weight is smooth on U, supporting
    T L v_s in Federer 4.1.1, p. 345. *)
Lemma distribution_partition_weight_class m (s:C m):
  norm_class_all_orders hNX (@scalar_absolute_value_norm R) U (v (val s)).
Proof.
move=>k.
exact:(@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) U (v (val s)) k (fun _ _=>Logic.I) hU
  (@smooth_partition_global_class R X NX hNX U J I v hv (val s)
    (@finite_exhaustion_subset J I C hC m (val s) (valP s)) k)).
Qed.

(** Source for [distribution_partition_partial_sum]: the
    actual finite sum of T L v_s over the original
    exhausting finite sets, Federer 4.1.1, p. 345. *)
Definition distribution_partition_partial_sum (T:DD) m:DD:=
  \sum_(s:C m) @distribution_scalar_restriction R X Y NX NY hNX hNY U hU E ev hE D hD
    (v (val s)) (@distribution_partition_weight_class m s) T.

(** Source for [distribution_partition_evaluations_eventually_exact]:
    each test sees exactly T from some partial sum onward,
    proving the original weak partition convergence of
    Federer 4.1.1, p. 345. No order, norm or
    absolute convergence is imposed on the distribution. *)
Theorem distribution_partition_evaluations_eventually_exact (T:DD) f:
  exists N,forall m,(N<=m)%N ->e (distribution_partition_partial_sum T m) f=e T f.
Proof.
have [K hK]:=smooth_test_support_bound hE f.
have [F [hFI hInactive]]:=smooth_partition_compact_active_selection hv K.
have [N hN]:=finite_exhaustion_captures_finite hC hFI.
exists N=>m hm.
pose P (s:C m):Hom DT DT:=@smooth_test_scalar_multiplier R X Y NX NY hNX hNY U E ev hE
  (v (val s)) (@distribution_partition_weight_class m s).
have hP s:is_smooth_multiplier U value (v (val s)) (P s).
  exact:(@smooth_test_scalar_multiplier_laws R X Y NX NY hNX hNY U E ev hE
    (v (val s)) (@distribution_partition_weight_class m s)).
have hFIc s:s \in C m ->I s:=@finite_exhaustion_subset J I C hC m s.
have hInactiveC x (hx:SmoothCompactSet.smooth_compact_carrier K x) s (hs:I s) (hn:s \notin C m):v s x=0.
  have hNotF:s \notin F.
    apply/negP=>hInF; have hInC: s \in C m:=(fsubsetP (hN m hm)) s hInF.
    by move:hn; rewrite hInC.
  exact:(hInactive x hx s hs hNotF).
have hIdentity:=@smooth_test_finite_partition_identity R X Y NX NY hNX hNY U E ev hE
  J I v hv K (C m) hFIc hInactiveC P hP f hK.
rewrite /distribution_partition_partial_sum linear_sum hom_sumE.
have hEval:(\sum_(s:C m) e (@distribution_scalar_restriction R X Y NX NY hNX hNY U hU E ev hE
  D hD (v (val s)) (@distribution_partition_weight_class m s) T) f)=\sum_(s:C m) e T (P s f).
  apply:eq_bigr=>s _.
  exact:(@distribution_scalar_restriction_evaluation R X Y NX NY hNX hNY U hU E ev hE D hD
    (v (val s)) (@distribution_partition_weight_class m s) T f).
by rewrite hEval -linear_sum hIdentity.
Qed.

(** Source for [distribution_partition_sum_weak]: the
    partial sums converge to T in the actual weak
    topology, Federer 4.1.1, p. 345. The filter
    is the ordinary natural-number tail filter. *)
Theorem distribution_partition_sum_weak (T:DD):
  open_family_converges DO ((fun m=>distribution_partition_partial_sum T m) @ \oo) T.
Proof.
have hF:Filter ((fun m=>distribution_partition_partial_sum T m) @ \oo):=
  fmap_filter _ (@filter_filter nat eventually eventually_filter).
have hWeak:=@WeakEvaluationTopology.convergence R DT DD (fun T f=>e T f)
  ((fun m=>distribution_partition_partial_sum T m) @ \oo) hF T.
apply (hWeak.2).
move=>f A hA hTf.
have [N hN]:=distribution_partition_evaluations_eventually_exact T f.
exists N; first exact Logic.I.
move=>m hm; change (A (e (distribution_partition_partial_sum T m) f)).
by rewrite (hN m hm).
Qed.
End DistributionPartition.

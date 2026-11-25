(** Federer (1969), 4.1.14, p. 370: the original flat
    convergence condition gives convergence on every original test
    and determines at most one actual current. The earlier finite
    dual bound supplies the proof; the test topology is unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation SmoothCompactSet
  CurrentFlatNorm CurrentFlatFormSeminormLaws CurrentFlatDualSeminormBasic
  CurrentFlatCompactMonotone CurrentFlatSequenceLimitUP CurrentWeakSequenceLimit
  FlatCurrentSpaces NormSequenceConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatSequenceLimits.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation DT:=(@current_test_space R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation Flat:=(@current_flat_test_seminorm R h2 n m U hU K).
Local Notation hFlat:=(@current_flat_test_is_seminorm R h2 n m U hU K).
Local Notation Limit:=(@is_current_flat_sequence_limit R h2 n m U hU K).

(** Source for [current_flat_sequence_limit_weak]: the F_E limit
    in Federer 4.1.14, p. 370, is the original weak current
    limit. No target membership, normality or measure representation
    is needed to pass to values on the original tests. *)
Theorem current_flat_sequence_limit_weak (u:nat->C) (T:C):
  Limit u T->@is_current_weak_sequence_limit R h2 n m U hU u T.
Proof.
move=>hLimit phi epsilon hEpsilon.
pose b:=Flat phi.
have hb:0<=b:=real_seminorm_nonnegative hFlat phi.
have hDenominator:0<b+1 by lra.
pose delta:=epsilon/(b+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[N hN]:=hLimit delta hDelta.
exists N=>j hNj.
have hSmall:=hN j hNj.
have hFinite:(F ((T-u j)%R) < +oo)%E:=lt_trans hSmall (ltry delta).
have[c [hc hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (action (T-u j)) hFinite.
have hReal:c<delta by move:hSmall;rewrite /current_flat_norm hValue lte_fin.
have hAction:=@current_flat_dual_finite_bound R h2 n m U hU K
  (action (T-u j)) c hValue phi.
pose E:=@current_point_evaluation R h2 n m U hU phi.
have hDifference:action (u j) phi-action T phi= -action (T-u j) phi.
  change (E (u j)-E T= -E (T-u j)).
  rewrite (linB (hom_linear E));ring.
rewrite hDifference normrN.
apply:(le_lt_trans hAction).
have hFirst:=ler_wpM2r hb (ltW hReal).
have hStrict:delta*b<delta*(b+1).
  rewrite (ltr_pM2l hDelta);lra.
have hEndpoint:delta*(b+1)=epsilon.
  by rewrite /delta divfK ?gt_eqF.
rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
Qed.

(** Source for [current_flat_sequence_limit_unique]: the original
    approximation condition can specify at most one actual current,
    Federer 4.1.14, p. 370. Use uniqueness on all original tests. *)
Theorem current_flat_sequence_limit_unique u (S T:C):
  Limit u S->Limit u T->S=T.
Proof.
move=>hS hT;apply:(@current_weak_sequence_limit_unique R h2 n m U hU u S T).
- exact:current_flat_sequence_limit_weak hS.
- exact:current_flat_sequence_limit_weak hT.
Qed.

(** Source for [current_flat_sequence_limit_constant]: a constant
    original smooth image sequence has its exact value, supporting
    agreement with the earlier smooth theory in 4.1.14, p. 370. *)
Lemma current_flat_sequence_limit_constant (T:C):Limit (fun _=>T) T.
Proof.
move=>epsilon hEpsilon;exists 0%N=>i _.
by rewrite subrr current_flat_norm_zero lte_fin.
Qed.

(** Source for [current_flat_sequence_limit_enlarge]: enlarging
    E preserves the original flat convergence, supporting the
    independence of the compact target neighbourhood in Federer
    4.1.14, pp. 370–371. The original dual seminorm decreases. *)
Theorem current_flat_sequence_limit_enlarge
    (L:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L)
    (u:nat->C) (T:C):
  Limit u T->@is_current_flat_sequence_limit R h2 n m U hU L u T.
Proof.
move=>hLimit epsilon hEpsilon;have[N hN]:=hLimit epsilon hEpsilon.
exists N=>i hNi.
exact:(le_lt_trans (@current_flat_compact_monotone R h2 n m U hU K L
  hKL (T-u i)) (hN i hNi)).
Qed.

(** Source for [flat_current_norm_sequence_limit]: the complete
    original flat space supplies the displayed F_E limit of actual
    currents, Federer 4.1.14, p. 370. Its public inclusion and
    exact norm law identify the two formulations. *)
Theorem flat_current_norm_sequence_limit
    (u:nat->@flat_current_space R h2 n m U hU K) z:
  ((fun i=>(u i:real_norm_metric_space
    (@flat_current_norm_is_norm R h2 n m U hU K))) @ \oo -->
      (z:real_norm_metric_space (@flat_current_norm_is_norm R h2 n m U hU K)))->
  Limit (fun i=>@flat_current_inclusion R h2 n m U hU K (u i))
    (@flat_current_inclusion R h2 n m U hU K z).
Proof.
move=>hConvergence epsilon hEpsilon.
have[N hN]:=(@norm_sequence_convergence_epsilon R
  (@flat_current_space R h2 n m U hU K)
  (@flat_current_norm R h2 n m U hU K)
  (@flat_current_norm_is_norm R h2 n m U hU K) u z).1
  hConvergence epsilon hEpsilon.
exists N=>i hNi.
rewrite -(linB (hom_linear (@flat_current_inclusion R h2 n m U hU K)))
  flat_current_norm_value lte_fin.
rewrite (real_seminorm_subtract (@flat_current_norm_is_norm R h2 n m U hU K).1).
exact:hN i hNi.
Qed.
End CurrentFlatSequenceLimits.

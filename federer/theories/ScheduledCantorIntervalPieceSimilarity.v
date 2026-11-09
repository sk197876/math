(** Federer (1969), 3.3.21, p. 309: actual original pieces retain the shifted original schedule. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeSpecial EqualCostIntervalTreeUnique EqualCostIntervalDescendants
  SpecialIntervalFamilyUP SpecialIntervalDescendantLimit SpecialIntervalLimitLaws
  AffineIntervalTransportUP AffineIntervalTransportExistence PositiveAffineClosedSegment
  PowerCantorTreeAffineTransport IntervalTreeLimitAffineTransport PowerConcaveIntervalGauge
  PowerCantorPairUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_interval_piece_similarity]: an
    actual original interval piece is the positive affine image of
    the actual unit-root Cantor factor with the SHIFTED original
    schedule, supporting 3.3.21, p. 309. Original Phi transport,
    recursion uniqueness and restricted original limits prove the
    identity. No constant-schedule self-similarity is assumed. *)
Theorem scheduled_original_interval_piece_similarity (R:realType) (c m a r:R)
    (J S:compact_real_intervals R) n H (A B:set (real_line_metric R)) (g:R->R) j:
  0<c ->0<m ->m<1 ->0<r ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_special_interval_tree_limit H A ->S \in H j ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->
  is_power_cantor_pair c m (fun k=>n (j+k)%N) B g ->
  exists M,is_affine_interval_transport a r M /\(fun x:R=>a+r * x) @` B=A `&` val S.
Proof.
move=>hc hm hm1 hr hTree hA hS hSValue [J0 [H0 [hJ0 [hTree0 [hB _]]]]].
have hGauge:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hGauge J n H hTree.
have [M hM]:=affine_interval_transport_exists a hr.
have hRoot:M J0=S.
  apply:val_inj;rewrite hM hJ0 positive_affine_closed_segment_image // !mulr0 !addr0 !mulr1.
  exact:esym hSValue.
have hImageTree:=@power_cantor_tree_positive_affine_transport R a r c m M J0
  (fun k=>n (j+k)%N) H0 hr hM hTree0.
rewrite hRoot in hImageTree.
have hDescTree:=@equal_cost_interval_original_descendants R _ hGauge J n H j S hTree hS.
have hLevels:=@equal_cost_interval_tree_unique R _ hGauge S (fun k=>n (j+k)%N) _ _ hDescTree hImageTree.
have hDescLimit:=@special_interval_original_descendant_limit R _ H A j S hSpecial hA hS.
rewrite hLevels in hDescLimit.
have hImageLimit:=@interval_tree_limit_positive_affine_transport R a r M H0 B hr hM hB.
exists M;split;first exact:hM.
exact:interval_tree_limit_unique hImageLimit hDescLimit.
Qed.

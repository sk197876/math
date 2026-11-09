(** Federer (1969), 3.3.20, pp. 307–308:
    every original binary Cantor piece is the exact positive similarity of the original set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeSpecial EqualCostIntervalTreeUnique EqualCostIntervalDescendants
  SpecialIntervalFamilyUP SpecialIntervalRefinement SpecialIntervalLimitLaws
  SpecialIntervalDescendantLimit AffineIntervalTransportUP AffineIntervalTransportExistence
  PositiveAffineClosedSegment PowerCantorTreeAffineTransport IntervalTreeLimitAffineTransport
  PowerConcaveIntervalGauge RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_piece_similarity]:
    the original-set similarities used in the
    projection partition argument and initial similarity
    reduction of 3.3.20, pp. 307–308.
    At every original interval S, all original
    descendant levels and the original restricted
    limit are exact positive affine images of the
    original unit-root levels and set A. Original
    Phi transport, recursion uniqueness and limit
    laws prove the identity. No self-similarity
    or replacement-fractal premise is assumed. *)
Theorem binary_cantor_original_piece_similarity (R:realType) (c m a r:R)
    (J S:compact_real_intervals R) H (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->0<r ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->S \in H j ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->
  exists M,is_affine_interval_transport a r M /\
    (forall k,special_interval_restriction (H (j+k)%N) (val S)=[fset M T|T in H k]) /\
    (fun x:R=>a+r * x) @` A=A `&` val S.
Proof.
move=>hc hm hm1 hr hJ hTree hA hS hSValue.
have hGauge:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hGauge J (fun _:nat=>2%N) H hTree.
have [M hM]:=affine_interval_transport_exists a hr.
have hRoot:M J=S.
  apply:val_inj;rewrite hM hJ positive_affine_closed_segment_image // !mulr0 !addr0 !mulr1.
  exact:esym hSValue.
have hImageTree:=@power_cantor_tree_positive_affine_transport R a r c m M J (fun _:nat=>2%N) H hr hM hTree.
rewrite hRoot in hImageTree.
have hDescTree:=@equal_cost_interval_original_descendants R _ hGauge J (fun _:nat=>2%N) H j S hTree hS.
have hLevels:=@equal_cost_interval_tree_unique R _ hGauge S (fun _:nat=>2%N) _ _ hDescTree hImageTree.
have hDescLimit:=@special_interval_original_descendant_limit R _ H A j S hSpecial hA hS.
rewrite hLevels in hDescLimit.
have hImageLimit:=@interval_tree_limit_positive_affine_transport R a r M H A hr hM hA.
have hLimit:=interval_tree_limit_unique hImageLimit hDescLimit.
exists M;split;first exact:hM.
split.
- move=>k;exact:(congr1 (fun L:nat->{fset compact_real_intervals R}=>L k) hLevels).
- exact:hLimit.
Qed.

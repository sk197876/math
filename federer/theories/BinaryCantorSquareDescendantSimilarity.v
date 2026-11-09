(** Federer (1969), 3.3.20, pp. 307–308: exact original descendant square families. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP SpecialIntervalRefinement BinaryCantorSquareLevelsUP
  BinaryCantorOriginalPieceSimilarity AffineIntervalTransportUP AffineIntervalTransportExistence
  FiniteCartesianImage RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_descendant_square_similarity]:
    the actual G_(j+k) descendants inside an original square are exactly
    the product similarity of the original G_k, 3.3.20, pp. 307–308.
    Factor recursion and original-set similarity prove the family identity;
    both auxiliary interval maps remain local existential witnesses. *)
Theorem binary_cantor_original_descendant_square_similarity (R:realType) (c m a b r:R)
    (J S T:compact_real_intervals R) H G (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->0<r ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  S \in H j ->T \in H j ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
  exists M N,is_affine_interval_transport a r M /\is_affine_interval_transport b r N /\
    injective (fun P:compact_real_intervals R*compact_real_intervals R=>(M P.1,N P.2)) /\
    forall k,((special_interval_restriction (H (j+k)%N) (val S)) `*`
      (special_interval_restriction (H (j+k)%N) (val T)))%fset=
      [fset (M P.1,N P.2)|P in G k].
Proof.
move=>hc hm hm1 hr hJ hTree hA hG hS hT hSValue hTValue.
have [M [hM [hMLevels _]]]:=@binary_cantor_original_piece_similarity R c m a r J S H A j
  hc hm hm1 hr hJ hTree hA hS hSValue.
have [N [hN [hNLevels _]]]:=@binary_cantor_original_piece_similarity R c m b r J T H A j
  hc hm hm1 hr hJ hTree hA hT hTValue.
have hMInjective:=affine_interval_transport_injective hr hM.
have hNInjective:=affine_interval_transport_injective hr hN.
exists M,N;split;first exact:hM.
split;first exact:hN.
split.
- move=>[U V] [W Z] hEqual.
  have hUW:=hMInjective U W (congr1 fst hEqual).
  have hVZ:=hNInjective V Z (congr1 snd hEqual).
  by rewrite hUW hVZ.
- move=>k;by rewrite hMLevels hNLevels finite_cartesian_image hG.
Qed.

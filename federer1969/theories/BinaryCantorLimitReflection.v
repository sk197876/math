(** Federer (1969), 3.3.20, pp. 306–307: the original Cantor factor is reflection invariant. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorLevelReflection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_cantor_factor_reflection]: actual
    original A is invariant under x maps to 1-x, supporting all
    projection directions of 3.3.20, pp. 306–307. Every original
    level has its reflected partner; the defining limit laws pass
    this fact to the original A, without replacing its construction. *)
Theorem binary_original_cantor_factor_reflection (R:realType) (c m:R)
    (J:compact_real_intervals R) H (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->forall x,A x <->A (1-x).
Proof.
move=>hc hm hm1 hJ hTree hA.
have hOne x:A x ->A (1-x).
  move=>hx;apply/(hA _).2=>j.
  have [S [hS hxS]]:=(hA x).1 hx j.
  have [T [hT hReflect]]:=@binary_original_interval_level_reflection R c m J H
    hc hm hm1 hJ hTree j S hS.
  exists T;split=>//;exact:(hReflect x).1 hxS.
move=>x;split;first exact:hOne.
move=>hx;have h:=hOne (1-x) hx.
have hUndo:1-(1-x)=x by ring.
by rewrite hUndo in h.
Qed.

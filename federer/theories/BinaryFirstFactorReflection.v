(** Federer (1969), 3.3.20, p. 307: reflection of the actual first-level factor union. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorLevelReflection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_first_factor_reflection]: the actual
    first original interval union is invariant under x maps to 1-x,
    supplying the complete first-projection U locus of 3.3.20, p. 307. *)
Lemma binary_original_first_factor_reflection (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  let B:=\bigcup_(S in [set` H 1%N]) val S in forall x,B x <->B (1-x).
Proof.
move=>hc hm hm1 hJ hTree B.
have hOne x:B x ->B (1-x).
  move=>[S hS hx].
  have [T [hT hReflect]]:=@binary_original_interval_level_reflection R c m J H hc hm hm1 hJ hTree 1%N S hS.
  exists T;first exact:hT.
  exact:(hReflect x).1 hx.
move=>x;split;first exact:hOne.
move=>hx;have h:=hOne (1-x) hx.
have hUndo:1-(1-x)=x by ring.
by rewrite hUndo in h.
Qed.

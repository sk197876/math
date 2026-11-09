(** Federer (1969), 3.3.20, pp. 306–307: actual critical first-level factor and reflection. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  CriticalFirstLevelIntervalSelection CriticalFirstLevelIntervals RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_first_level_factor]: the union of the two
    actual first-level factor intervals at m=1/2, 3.3.20, pp. 306–307.
    Its identification with the original H_1 is proved separately. *)
Definition critical_first_level_factor (R:realType):set (real_line_metric R):=
  (`[0,1/4] `|` `[3/4,1])%classic.

(** Source for [critical_original_first_level_factor_union]: the actual
    original H_1 union is the two printed quarter intervals, as used
    for the square symmetries in 3.3.20, pp. 306–307. *)
Theorem critical_original_first_level_factor_union (R:realType) (c:R)
    (J:compact_real_intervals R) H:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  (\bigcup_(S in [set` H 1%N]) val S)=(@critical_first_level_factor R).
Proof.
move=>hc hJ hTree.
have hCharacter:=@critical_original_first_level_intervals R c J H hc hJ hTree.
have [I [_ [hI _]]]:=@critical_first_level_original_interval_selection R c J H hc hJ hTree.
have hLeft:val (I false)=(`[0,1/4]:set (real_line_metric R))
  by rewrite (hI false).2 /critical_first_level_coordinate add0r.
have hRight:val (I true)=(`[3/4,1]:set (real_line_metric R)).
  rewrite (hI true).2 /critical_first_level_coordinate.
  have hEnd:(3/4:R)+1/4= 1 by lra.
  by rewrite hEnd.
apply/seteqP;split=>x.
- move=>[S hS hx];have [hValue|hValue]:=(hCharacter S).1 hS;
    [left|right];by rewrite -hValue.
- move=>[hx|hx].
  + exists (I false);first exact:(hI false).1.
    by rewrite hLeft.
  + exists (I true);first exact:(hI true).1.
    by rewrite hRight.
Qed.

(** Source for [critical_first_level_factor_reflection]: the actual
    first-level factor is invariant under x maps to 1-x, supporting
    the original square symmetries in 3.3.20, p. 307. *)
Lemma critical_first_level_factor_reflection (R:realType) (x:R):
  (@critical_first_level_factor R) x <->(@critical_first_level_factor R) (1-x).
Proof.
rewrite /critical_first_level_factor /= !in_itv /=.
split;move=>[/andP[h0 h1]|/andP[h0 h1]];
  [right|left|right|left];apply/andP;split;lra.
Qed.

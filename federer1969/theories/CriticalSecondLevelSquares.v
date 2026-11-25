(** Federer (1969), 3.3.20, p. 308:
    all sixteen actual original squares in the initial Omega argument. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorSquareLevelsUP CriticalSecondLevelIntervals RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_second_level_original_squares]:
    the original level-two squares used in
    the (2,8,4,11/16) and (2,8,1,7/8)
    Omega certificates of 3.3.20, p. 308.
    A local four-boolean index retains both actual
    parent coordinates and both actual child coordinates.
    Membership, exact endpoints and injection are
    proved from the original interval recursion. *)
Theorem critical_second_level_original_squares (R:realType) (c:R)
    (J:compact_real_intervals R) H G:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  exists Q:((bool*bool)*(bool*bool))->(compact_real_intervals R*compact_real_intervals R),
    injective Q /\(forall k,Q k \in G 2%N) /\
    forall k,val (Q k).1=
      (`[critical_second_level_coordinate R k.1.1 k.2.1,
        critical_second_level_coordinate R k.1.1 k.2.1+1/16]:set (real_line_metric R)) /\
      val (Q k).2=
      (`[critical_second_level_coordinate R k.1.2 k.2.2,
        critical_second_level_coordinate R k.1.2 k.2.2+1/16]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree hG.
have [D [hInjective hD]]:=@critical_second_level_original_intervals R c J H hc hJ hTree.
pose Q (k:(bool*bool)*(bool*bool)):=(D k.1.1 k.2.1,D k.1.2 k.2.2).
exists Q;split.
- move=>[[b d] [t u]] [[e f] [v w]] hEqual.
  have hFirst:=hInjective (b,t) (e,v) (congr1 fst hEqual).
  have hSecond:=hInjective (d,u) (f,w) (congr1 snd hEqual).
  have hBE:=congr1 fst hFirst.
  have hTV:=congr1 snd hFirst.
  have hDF:=congr1 fst hSecond.
  have hUW:=congr1 snd hSecond.
  rewrite /= in hBE hTV hDF hUW.
  by rewrite hBE hTV hDF hUW.
split.
- move=>k;rewrite hG in_fsetM /Q /=;apply/andP;split;exact:(hD _ _).1.
- move=>k;split;exact:(hD _ _).2.
Qed.

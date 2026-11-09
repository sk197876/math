(** Federer (1969), 3.3.20, pp. 306–308:
    exhaustive local indexing of the four actual original first-level squares. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorSquareLevelsUP CriticalFirstLevelIntervalSelection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_first_level_original_squares]:
    the four original G_1 corner squares in
    3.3.20, pp. 306–308. Their
    local boolean indexing is injective, exhaustive,
    and has the exact original closed endpoints.
    These laws are proved from the original
    interval recursion; no replacement square family
    or geometric certificate is assumed. *)
Theorem critical_first_level_original_squares (R:realType) (c:R)
    (J:compact_real_intervals R) H G:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  exists Q:bool*bool->(compact_real_intervals R*compact_real_intervals R),
    injective Q /\(forall k,Q k \in G 1%N) /\
    (forall P,P \in G 1%N ->exists k,P=Q k) /\
    forall k,val (Q k).1=
      (`[critical_first_level_coordinate R k.1,critical_first_level_coordinate R k.1+1/4]:set (real_line_metric R)) /\
      val (Q k).2=
      (`[critical_first_level_coordinate R k.2,critical_first_level_coordinate R k.2+1/4]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree hG.
have [I [hInjective [hI hExhaust]]]:=@critical_first_level_original_interval_selection R c J H hc hJ hTree.
pose Q (k:bool*bool):=(I k.1,I k.2).
exists Q;split.
- move=>[b d] [e f] hEqual.
  have hBE:=hInjective b e (congr1 fst hEqual).
  have hDF:=hInjective d f (congr1 snd hEqual).
  by rewrite hBE hDF.
split.
- move=>k;rewrite hG in_fsetM /Q /=;apply/andP;split;exact:(hI _).1.
split.
- move=>[S T];rewrite hG in_fsetM=>/andP[hS hT].
  have [b hB]:=hExhaust S hS.
  have [d hD]:=hExhaust T hT.
  exists (b,d);by rewrite /Q /= -hB -hD.
- move=>k;split;exact:(hI _).2.
Qed.

(** Federer (1969), 3.3.20, p. 308:
    the actual two-level corner geometry used in the initial Omega cases. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  CriticalCornerCoordinate CriticalCornerIntervalSelection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_second_level_coordinate]: supporting
    exact lower coordinate of an ORIGINAL level-two
    interval in 3.3.20, p. 308. The
    first boolean chooses its original first-level
    parent, the second its original child. *)
Definition critical_second_level_coordinate (R:realType) (b t:bool):R:=
  (if b then 3/4 else 0)+(if t then 3/16 else 0).

(** Source for [critical_second_level_original_intervals]:
    the four actual intervals with lower endpoints
    0,3/16,3/4,15/16 in 3.3.20,
    p. 308. A local selection has
    proved original membership, exact width 1/16
    and injection. No replacement construction or
    supplied finite-stage geometry is used. *)
Theorem critical_second_level_original_intervals (R:realType) (c:R)
    (J:compact_real_intervals R) H:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  exists D:bool->bool->compact_real_intervals R,
    injective (fun p:bool*bool=>D p.1 p.2) /\
    forall b t,D b t \in H 2%N /\val (D b t)=
      (`[critical_second_level_coordinate R b t,
        critical_second_level_coordinate R b t+1/16]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree.
have [C hC]:=@critical_corner_original_interval_selection_exists R c J H 2 hc hJ hTree (erefl true).
have hPower:(4:R)^+2= 16 by ring.
rewrite hPower in hC.
pose offset (b t:bool):nat:=if xorb b t then 3 else 0.
pose D b t:=C b (offset b t).
have hOffset b t:offset b t \in [::0;3;12;15] by case:b;case:t;by [].
have hSize b t:((offset b t+1)%:R:R)/16<=1/4.
  by case:b;case:t;rewrite /offset /=;lra.
have hLow b t:critical_corner_coordinate 16 b (offset b t)=critical_second_level_coordinate R b t.
  by case:b;case:t;rewrite /offset /critical_corner_coordinate /critical_second_level_coordinate /=;
    field;rewrite ?pnatr_eq0.
have hOffsetInjective b t u:offset b t=offset b u ->t=u.
  by case:b;case:t;case:u=>//.
exists D;split.
- move=>[b t] [d u] hEqual.
  have hSixteen:0<(16:R) by rewrite ltr0n.
  have [hParent hChild]:=@critical_corner_interval_selection_injective R 16 (H 2%N) C hC hSixteen
    b d (offset b t) (offset d u) (hOffset b t) (hOffset d u) (hSize b t) (hSize d u) hEqual.
  subst d;have hTU:=hOffsetInjective b t u hChild.
  by rewrite hTU.
- move=>b t;have [hMember hValue]:=hC b (offset b t) (hOffset b t).
  split=>//;by rewrite hLow in hValue.
Qed.

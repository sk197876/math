(** Federer (1969), 3.2.40, p. 276, using
    A(m,n) from 2.10.28, p. 193: multiplication of
    the power gauge by a positive constant changes no
    actual equal-cost interval subdivision or tree. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealPower CantorSplitRadiusUP
  EqualCostIntervalFamilyUP EqualCostIntervalTreeUP CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_split_coefficient_change]: supporting
    coefficient independence of the original set A(m,n) used
    by Federer 3.2.40, p. 276. The positive coefficient
    cancels from the original equal-cost equation in
    2.10.28(4), p. 192. Bounds and the actual child
    width are retained exactly. *)
Lemma power_cantor_split_coefficient_change (R:realType) (c d m a s:R) n:
  0<c ->0<d ->is_cantor_split_radius (fun t=>c*real_power t m) a n s ->
  is_cantor_split_radius (fun t=>d*real_power t m) a n s.
Proof.
move=>hc hd hSplit; constructor; first exact:cantor_split_radius_bounds hSplit.
have hcNonzero:c!=0 by rewrite gt_eqF.
have hBase:real_power s m=real_power a m/n%:R.
  apply:(mulfI hcNonzero).
  by rewrite (cantor_split_radius_cost hSplit) mulrA.
by rewrite hBase mulrA.
Qed.

(** Source for [power_cantor_family_coefficient_change]: supporting
    the original geometric carrier in Federer 3.2.40, p. 276.
    Every interval, endpoint, index and spacing of Phi is
    unchanged under positive gauge scaling; only its scalar
    cost equation is multiplied by the new coefficient. *)
Lemma power_cantor_family_coefficient_change (R:realType) (c d m:R)
    (J:compact_real_intervals R) n F:
  0<c ->0<d ->is_equal_cost_interval_family (fun t=>c*real_power t m) J n F ->
  is_equal_cost_interval_family (fun t=>d*real_power t m) J n F.
Proof.
move=>hc hd [hn [a [b [s [t [hJ [hParent [hSplit [hSpacing hValues]]]]]]]]].
split; first exact hn.
exists a,b,s,t; split=>//; split=>//; split.
- exact:power_cantor_split_coefficient_change hc hd hSplit.
- by split.
Qed.

(** Source for [power_cantor_tree_coefficient_change]: supporting
    preservation of every actual level of A(m,n) in Federer
    3.2.40, p. 276. The original root and the same
    finite child families prove the new recurrence laws.
    No tree implementation is unfolded or reselected. *)
Lemma power_cantor_tree_coefficient_change (R:realType) (c d m:R) J n H:
  0<c ->0<d ->is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  is_equal_cost_interval_tree (fun t=>d*real_power t m) J n H.
Proof.
move=>hc hd hTree; constructor; first exact:equal_cost_tree_root hTree.
move=>j; have [K [hK hNext]]:=equal_cost_tree_step hTree j.
exists K; split; last exact hNext.
move=>S hS; exact:power_cantor_family_coefficient_change hc hd (hK S hS).
Qed.

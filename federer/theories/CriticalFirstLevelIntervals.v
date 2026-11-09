(** Federer (1969), 3.3.20, pp. 306–308:
    exact original critical first-level intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalRefinement BinaryCantorIntervalChildren CriticalCantorRatio RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_first_level_intervals]:
    the original first-level factor intervals
    [0,1/4] and [3/4,1] of
    3.3.20, pp. 306–308. The
    original Phi law and actual half-power
    split radius identify ALL first-level members;
    no replacement interval family is supplied. *)
Theorem critical_original_first_level_intervals (R:realType) (c:R)
    (J:compact_real_intervals R) H:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  forall S:compact_real_intervals R,S \in H 1%N <->
    val S=(`[0,1/4]:set (real_line_metric R)) \/val S=(`[3/4,1]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have [K [hK hStep]]:=equal_cost_tree_step hTree 0%N.
have hRoot:J \in H 0%N by rewrite (equal_cost_tree_root hTree) in_fset1.
have hChildren:=@binary_cantor_interval_children R c (1/2:R) 0 1 J (K J)
  hc hm hm1 ltr01 hJ (hK J hRoot).
rewrite critical_cantor_binary_ratio subr0 mul1r in hChildren.
cbn zeta in hChildren.
rewrite add0r in hChildren.
have hRight:(1:R)-1/4=3/4 by field;rewrite ?pnatr_eq0.
rewrite mul1r in hRight.
rewrite hRight in hChildren.
move=>S;rewrite !mul1r;split.
- move=>hS;rewrite hStep in hS.
  have [P [hP hChild]]:=(@special_interval_refinement_membership R (H 0%N) K S).1 hS.
  have hPJ:P=J by move:hP;rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP.
  subst P.
  exact:(hChildren S).1 hChild.
- move=>hS;rewrite hStep;apply/special_interval_refinement_membership;exists J;split=>//.
  exact:(hChildren S).2 hS.
Qed.

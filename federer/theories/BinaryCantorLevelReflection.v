(** Federer (1969), 3.3.20, pp. 306–307: reflection of every original binary interval level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter MetricDiameterReal
  EqualCostIntervalTreeUP EqualCostIntervalTreeLaws SpecialIntervalRefinement
  BinaryReflectedIntervalChildren RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_interval_level_reflection]: every
    actual original interval has its reflected partner at the same
    level, supporting all directions of 3.3.20, pp. 306–307. Induction
    uses the original Phi recurrence and its reflected endpoint children. *)
Theorem binary_original_interval_level_reflection (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  forall j S,S \in H j ->exists T,T \in H j /\forall x,val S x <->val T (1-x).
Proof.
move=>hc hm hm1 hJ hTree;elim=>[S|j ih S] hS.
- move:hS;rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP->.
  exists J;split;first by rewrite in_fset1.
  move=>x;rewrite hJ /= !in_itv /=.
  split=>/andP[h0 h1];apply/andP;split;lra.
- have [K [hK hNext]]:=equal_cost_tree_step hTree j.
  rewrite hNext in hS.
  have [P [hP hChild]]:=(@special_interval_refinement_membership R (H j) K S).1 hS.
  have [Q [hQ hReflect]]:=ih P hP.
  have [a [b [hab hValueP]]]:=set_valP P.
  have hPositive:=@equal_cost_tree_member_positive R _ J (fun _:nat=>2%N) H hTree j P hP.
  rewrite hValueP (extended_metric_diameter_segment hab) in hPositive.
  change (is_true (0<b-a)) in hPositive.
  have habStrict:a<b by lra.
  have hValueQ:val Q=(`[1-b,1-a]:set (real_line_metric R)).
    apply/seteqP;split=>x hx.
    + have hUndo:1-(1-x)=x by ring.
      have hy:val P (1-x) by apply:(hReflect (1-x)).2;by rewrite hUndo.
      move:hy;rewrite hValueP /= in_itv /= =>/andP[h0 h1].
      change (is_true (1-b<=x<=1-a));apply/andP;split;lra.
    + have hUndo:1-(1-x)=x by ring.
      rewrite -hUndo;apply:(hReflect (1-x)).1.
      move:hx;rewrite hValueP /= !in_itv /= =>/andP[h0 h1].
      apply/andP;split;lra.
  have [T [hT hTS]]:=@binary_original_reflected_interval_children R c m a b P Q
    (K P) (K Q) S hc hm hm1 habStrict hValueP hValueQ (hK P hP) (hK Q hQ) hChild.
  exists T;split=>//;rewrite hNext;apply/special_interval_refinement_membership.
  by exists Q.
Qed.

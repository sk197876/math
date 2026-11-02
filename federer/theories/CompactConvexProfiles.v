(** Federer (1969), 2.10.21, p. 184: a nonempty compact subset C of a normed
    vector space is convex if and only if its distance profile is convex.
    Prove the forward inequality with nearest points and the norm triangle
    law; the converse follows from the zero-set identity. This part needs no
    finite dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric InnerConvex ConvexFunctionUP
  CompactSetDistanceProfile CompactProfileNearest MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_distance_profile]: direct
    convex-set/convex-profile equivalence in 2.10.21,
    p. 184. It holds in any real normed
    vector space for nonempty compact C. *)
Theorem compact_convex_distance_profile (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (C : compact_metric_set (real_norm_metric_space hN)) :
  is_inner_convex (val C) <-> is_real_convex_function_on setT (compact_set_distance_profile C).
Proof.
split.
- move=> hC; split; first by move=> x y hx hy t ht ht1.
  move=> x y _ _ t ht ht1.
  have [u [hu hxu]] := compact_profile_nearest_point C x.
  have [v [hv hyv]] := compact_profile_nearest_point C y.
  have hw := hC u v hu hv t ht ht1.
  have hbound := @metric_set_distance_lower R (real_norm_metric_space hN) (val C)
    (compact_set_distance_profile C) (compact_set_distance_profile_specification C)
    ((1-t)*:x+t*:y) ((1-t)*:u+t*:v) hw.
  change (N (x-u)=compact_set_distance_profile C x) in hxu.
  change (N (y-v)=compact_set_distance_profile C y) in hyv.
  change (is_true (compact_set_distance_profile C ((1-t)*:x+t*:y)<=
    N ((1-t)*:x+t*:y-((1-t)*:u+t*:v)))) in hbound.
  have h1t : 0<=1-t by rewrite subr_ge0.
  have he : (1-t)*:x+t*:y-((1-t)*:u+t*:v)=(1-t)*:(x-u)+t*:(y-v).
    by rewrite !scalerBr opprD addrACA.
  rewrite he in hbound.
  have htri := real_seminorm_triangle hN.1 ((1-t)*:(x-u)) (t*:(y-v)).
  rewrite !(real_seminorm_scale hN.1) (ger0_norm h1t) (ger0_norm ht) hxu hyv in htri.
  exact: le_trans hbound htri.
- move=> [_ hC] x y hx hy t ht ht1.
  have hineq := hC x y I I t ht ht1.
  have hzx := proj2 (compact_set_distance_profile_zero C x) hx.
  have hzy := proj2 (compact_set_distance_profile_zero C y) hy.
  rewrite hzx hzy !mulr0 addr0 in hineq.
  apply: (proj1 (compact_set_distance_profile_zero C ((1-t)*:x+t*:y))).
  apply/eqP; rewrite eq_le hineq (metric_set_distance_nonnegative
    (compact_set_distance_profile_specification C) ((1-t)*:x+t*:y)).
  by [].
Qed.

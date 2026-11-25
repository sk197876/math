(** Federer (1969), 1.7.13, p. 37: the diameter bound diam(C_s)<=2s, from
    convexity and the parallelogram identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerSetDistanceUP InnerConvex InnerNearSet InnerMidpointParallelogram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Diameter.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable a : M.
Variable C : set M.
Variable d : R.
Hypothesis hd : is_inner_set_distance hB a C d.
Hypothesis hconv : is_inner_convex C.

(** Source for [inner_near_diameter]: Federer 1.7.13,
    p. 37, conclusion of the displayed estimate: two points
    in C_s have distance at most 2s. No completeness or
    closedness is used for this estimate. *)
Theorem inner_near_diameter s (hs : 0 < s) x y :
    inner_near_set hB a C d s x -> inner_near_set hB a C d s y ->
    inner_norm hB (x-y) <= 2*s.
Proof.
move=> [hx hnx] [hy hny].
have hm := inner_convex_midpoint hconv hx hy.
have hlow := @inner_set_distance_lower_law R V B hB a C d hd _ hm.
have hlow2 : d^+2 <= inner_norm hB (a-(2:R)^-1 *: (x+y))^+2.
  by rewrite (ler_sqr (inner_set_distance_nonnegative_law hd) (inner_norm_nonnegative hB _)).
have hu := lerD hnx hny.
have he : forall q : R, 2*(q+q)=4*q.
  move=> q; by rewrite -(mulr2n q) -(mulr_natl q 2) mulrA -natrM.
have h2p : (0 : R) < 2 by rewrite ltr0n.
have h4p : (0 : R) < 4 by rewrite ltr0n.
have hu2 : 2*(inner_norm hB (a-x)^+2+inner_norm hB (a-y)^+2) <= 2*((d^+2+s^+2)+(d^+2+s^+2)).
  by rewrite ler_pM2l.
have hp := inner_midpoint_parallelogram hB a x y.
have hlo4 : 4*d^+2 <= 4*inner_norm hB (a-(2:R)^-1 *: (x+y))^+2.
  by rewrite ler_pM2l.
have hsum := lerD hlo4 (lexx (inner_norm hB (x-y)^+2)).
rewrite hp in hsum.
have hh := le_trans hsum hu2.
rewrite he mulrDr lerD2l in hh.
rewrite -(ler_sqr (inner_norm_nonnegative hB _) (mulr_ge0 (ler0n R 2) (ltW hs)))
  exprMn [(2:R)^+2]expr2 -natrM.
exact hh.
Qed.
End Diameter.

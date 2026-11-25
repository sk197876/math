(** Federer (1969), 2.4.12, p. 87: private finite Borel approximation
    witness on compact sets. A finite ball cover supplies candidates; the
    previously sealed nearest-prefix laws supply their Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import CompactFiniteCover MetricClosedBalls FiniteNearestApproximationUP
  FiniteNearestApproximationSealed FiniteNearestApproximation CompactFiniteApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_finite_approximation_exists]: supporting
    finite-partition existence in Federer 2.4.12, p. 87 A compact set has a
    finite cover by epsilon balls; including a distinguished point in the
    candidate list yields the additional reference-error bound. *)
Theorem compact_finite_approximation_exists (R : realType) (Y : metricType R)
    (K : set Y) (epsilon : R) (y0 : Y) :
  compact K -> 0 < epsilon -> exists a, is_compact_finite_approximation K epsilon y0 a.
Proof.
move=> hK he.
pose U z := [set x : Y | mdist z x < epsilon].
have hcover : K `<=` \bigcup_(z in K) U z.
  move=> x hx; exists x=> //; by rewrite /U /= mdistxx.
have hopen z : K z -> open (U z) by move=> _; exact: metric_open_ball_open.
have [F hF hcov] := compact_open_finite_cover hK hopen hcover.
pose s : seq Y := y0 :: F.
pose y n := nth y0 s n.
pose q := @FiniteNearestApproximation.value R Y y.
have hq := @FiniteNearestApproximation.laws R Y y.
pose n := size (F : seq Y).
pose a x := y (q n x).
exists a; constructor.
- exact: finite_nearest_map_borel hq n.
- exact: finite_nearest_map_finite_image hq n.
- move=> x; exact: finite_nearest_map_reference_bound hq n x.
- move=> x hx; have [z hz hzx] := hcov x hx.
  have hzs : z \in s by rewrite /s in_cons hz orbT.
  have hi : (index z s <= n)%N.
    have hh : (index z s < size s)%N by rewrite index_mem.
    exact hh.
  have hb := @finite_nearest_minimal R Y y q hq n x (index z s) hi.
  rewrite /y nth_index // in hb.
  apply: le_lt_trans hb _; rewrite metric_sym; exact hzx.
Qed.

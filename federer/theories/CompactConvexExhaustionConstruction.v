(** Private existence proof for the exhaustion supporting Federer (1969),
    2.10.32, pp. 196–197. Intersect a nonempty closed convex target with
    increasing closed balls about one of its points. Bounded compactness
    supplies compactness; convexity and the Archimedean property supply the
    remaining abstract laws. The centre and natural radii are implementation
    choices hidden by the subsequent opaque interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerConvex
  RealNormUP NormConvexHullDiameter MetricClosedBalls LipschitzFunctionCompact
  CompactSetDistanceProfile CompactConvexExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_exhaustion_exists]: supporting
    existence of the compact convex reduction
    for the unrestricted assertion in 2.10.32,
    pp. 196–197. Bounded compactness is explicit;
    the Euclidean instance will prove it from
    the existing finite-dimensional theorem. *)
Theorem compact_convex_exhaustion_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (C : set (inner_metric_space hB)) :
  metric_boundedly_compact (inner_metric_space hB) -> C !=set0 -> closed C -> is_inner_convex C ->
  exists A : nat -> compact_metric_set (inner_metric_space hB), is_compact_convex_exhaustion hB C A.
Proof.
move=> hX [a ha] hC hconv.
pose X : metricType R := [the metricType R of inner_metric_space hB].
pose D (k : nat) : set X := C `&` @metric_closed_ball R X a (k%:R : R).
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
have hball k : is_inner_convex (metric_closed_ball a (k%:R : R)).
  have he : metric_closed_ball a (k%:R : R)=[set x : X | inner_norm hB (x-a)<=k%:R].
    by apply/seteqP; split=> x; rewrite /metric_closed_ball /= inner_metric_distanceE -[a-x]opprB inner_normN.
  rewrite he; exact (@norm_ball_inner_convex R V (inner_norm hB) hN a k%:R).
have hDc k : compact (D k).
  have hclosed : closed (D k) := closedI hC (@metric_closed_ball_closed R X a (k%:R : R)).
  have hcomp : compact (@metric_closed_ball R X a (k%:R : R)) := hX a k%:R (ler0n _ _).
  apply: (subclosed_compact hclosed hcomp)=> x hx; exact hx.2.
have hDne k : D k !=set0.
  exists a; split=> //; by rewrite /metric_closed_ball /= mdistxx ler0n.
pose A k : compact_metric_set X := exist _ (D k) (mem_set (conj (hDc k) (hDne k))).
exists A; constructor.
- move=> k x y hx hy t ht ht1; split.
  + exact (hconv x y hx.1 hy.1 t ht ht1).
  + exact (hball k x y hx.2 hy.2 t ht ht1).
- by move=> k x hx; exact hx.1.
- move=> k l hkl x hx; split; first exact hx.1.
  change (is_true (mdist a x<=l%:R)).
  apply: le_trans hx.2 _; by rewrite ler_nat.
- move=> x hx.
  exists (Num.bound (mdist a x)); first by [].
  split=> //; exact: ltW (archi_boundP (mdist_ge0 a x)).
Qed.

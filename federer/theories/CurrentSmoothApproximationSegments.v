(** Federer (1969), 4.1.14, p. 370: the proof first
    compares two smooth approximations on the original compact
    support. Uniform convergence keeps their affine segments
    inside every prescribed compact target neighbourhood; only
    the original K derivative caps are used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP NormBoundedLinearTopology InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet SmoothCompactImage MetricOpenThickening
  MetricCompactNeighbourhood NormOpenBallAffineSegment
  CurrentSmoothApproximationUP CurrentMapDifferential EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothApproximationComparison.
Variable R : realType.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z : set X) (V : set Y).
Variable K : smooth_compact_set hNX Z.
Variable f : X -> Y.
Variables g q : nat -> X -> Y.
Hypothesis hG : @is_current_smooth_approximation R n nu Z V K f g.
Hypothesis hQ : @is_current_smooth_approximation R n nu Z V K f q.

(** Source for [current_smooth_approximation_difference]: two
    original uniformly convergent families approach one another
    on the same K, Federer 4.1.14, p. 370. *)
Lemma current_smooth_approximation_difference (epsilon : R) :
  0<epsilon -> exists N : nat, forall i j : nat,
    (N<=i)%N -> (N<=j)%N -> forall x,
    smooth_compact_carrier K x -> NY (q j x-g i x)<epsilon.
Proof.
move=> he.
have hHalf : 0<epsilon/2 by rewrite divr_gt0 // ltr0n.
have [Ng hNg] := current_smooth_approximation_uniform hG hHalf.
have [Nq hNq] := current_smooth_approximation_uniform hQ hHalf.
exists (maxn Ng Nq) => i j hi hj x hx.
have hGx := hNg i (leq_trans (leq_maxl _ _) hi) x hx.
have hQx := hNq j (leq_trans (leq_maxr _ _) hj) x hx.
have hTriangle := @metric_triangle R (real_norm_metric_space hNY)
  (q j x) (f x) (g i x).
change (is_true (NY (q j x-g i x) <= NY (q j x-f x)+NY (f x-g i x)))
  in hTriangle.
rewrite (real_seminorm_subtract hNY.1 (g i x) (f x)) in hGx.
by lra.
Qed.

(** Source for [current_smooth_approximation_common_derivative_cap]:
    the two original K-only caps have one positive common bound,
    Federer 4.1.14, p. 370. No bound outside K is added. *)
Lemma current_smooth_approximation_common_derivative_cap :
  exists c : R, 1<=c /\ forall i j x,
    smooth_compact_carrier K x ->
    Num.max
      (@euclidean_operator_norm R n nu
        (@current_map_differential R n nu Z (g i) x))
      (@euclidean_operator_norm R n nu
        (@current_map_differential R n nu Z (q j) x)) <= c.
Proof.
have [a [ha hGa]] := current_smooth_approximation_bound hG.
have [b [hb hQb]] := current_smooth_approximation_bound hQ.
exists (a+b+1); split; first by lra.
move=> i j x hx; rewrite ge_max; apply/andP; split.
- have hA : a<=a+b+1 by lra.
  exact: le_trans (hGa i x hx) hA.
- have hB : b<=a+b+1 by lra.
  exact: le_trans (hQb j x hx) hB.
Qed.

(** Source for [current_smooth_approximation_segments]: the
    original comparison segments eventually lie in every given
    compact E whose interior contains f(K), Federer 4.1.14,
    p. 370. The source may be arbitrary open, and E may be
    nonconvex. Empty K needs no selected source or target point. *)
Theorem current_smooth_approximation_segments
    (hImage : forall x, Z x -> V (f x))
    (hf : norm_class_zero NX NY Z f)
    (E : smooth_compact_set hNY V)
    (hInterior : forall x, smooth_compact_carrier K x ->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)) :
  exists N : nat, forall i j : nat, (N<=i)%N -> (N<=j)%N ->
    forall x t, smooth_compact_carrier K x -> 0<=t -> t<=1 ->
    smooth_compact_carrier E ((1-t)*:g i x+t*:q j x).
Proof.
pose fK := @smooth_compact_image R X Y NX NY hNX hNY Z V f hImage hf K.
pose O := @interior (real_norm_metric_space hNY) (smooth_compact_carrier E).
have hIn : smooth_compact_carrier fK `<=` O.
  move=> y [x hx <-].
  exact: (norm_domain_interior_neighbourhood hNY _ _).1 (hInterior x hx).
have [r [hr hTube]] := @compact_metric_open_thickening R
  (real_norm_metric_space hNY) (smooth_compact_carrier fK) O
  (smooth_compact_is_compact fK) (open_interior _) hIn.
have [Ng hNg] := current_smooth_approximation_uniform hG hr.
have [Nq hNq] := current_smooth_approximation_uniform hQ hr.
exists (maxn Ng Nq) => i j hi hj x t hx ht ht1.
have hGx := hNg i (leq_trans (leq_maxl _ _) hi) x hx.
have hQx := hNq j (leq_trans (leq_maxr _ _) hj) x hx.
have hSegment := @norm_open_ball_affine_segment R Y NY hNY (f x)
  (g i x) (q j x) r t hGx hQx ht ht1.
have hO : O ((1-t)*:g i x+t*:q j x).
  apply: hTube; exists (f x); first by exists x.
  change (is_true (NY (f x-((1-t)*:g i x+t*:q j x))<r)).
  by rewrite (real_seminorm_subtract hNY.1).
exact: interior_subset hO.
Qed.
End SmoothApproximationComparison.

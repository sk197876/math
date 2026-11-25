(** Federer (1969), 3.2.47(1), p. 283: supporting
    bounded product parameters for genuine rectifiability. The
    actual Euclidean block metric and its triangle inequality
    give the bound, without a closure or measurability hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormInequalities
  EuclideanBlockLinearMaps EuclideanBlockNorms EuclideanCartesianMap
  CoveringFamilyUP CoveringFamilyLaws MetricBoundedUnion MetricBoundedClosureLaws MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_norm_triangle]: the actual
    norm of a block vector is at most the sum of
    its block norms, supporting the bounded product domain
    in 3.2.47(1), p. 283. Empty blocks are retained. *)
Lemma euclidean_block_norm_triangle (R:realType) m n (x:R_n R (m+n)):
  inner_norm (@euclidean_inner_productP R (m+n)) x<=
    inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m n x)+
    inner_norm (@euclidean_inner_productP R n) (@euclidean_last_block R m n x).
Proof.
have hDecomposition:=@euclidean_block_linear_decomposition R m n x.
have hTriangle:=@inner_norm_triangle R (R_n R (m+n)) _ (@euclidean_inner_productP R (m+n))
  (@euclidean_first_injection R m n (@euclidean_first_block R m n x))
  (@euclidean_last_injection R m n (@euclidean_last_block R m n x)).
rewrite -hDecomposition euclidean_first_injection_norm euclidean_last_injection_norm in hTriangle.
exact hTriangle.
Qed.

(** Source for [euclidean_bounded_cartesian_product]: two bounded
    original parameter domains have bounded actual block product,
    supporting genuine rectifiability in 3.2.47(1), p. 283,
    including empty and zero-dimensional factors. *)
Theorem euclidean_bounded_cartesian_product (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  metric_set_bounded A ->metric_set_bounded B ->
  @metric_set_bounded R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (euclidean_cartesian_set A B).
Proof.
move=>hA hB.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+n)).
have [r [hr hRadiusA]]:=@metric_bounded_distance_bound R
  (inner_metric_space (@euclidean_inner_productP R m)) A 0 hA.
have [s [hs hRadiusB]]:=@metric_bounded_distance_bound R
  (inner_metric_space (@euclidean_inner_productP R n)) B 0 hB.
have hBall:@metric_set_bounded R X (metric_closed_ball (0:X) (r+s)).
  exact (@covering_closed_ball_bounded R X 0 (r+s) (addr_ge0 hr hs)).
apply:(@metric_bounded_subset R X (euclidean_cartesian_set A B)
  (metric_closed_ball (0:X) (r+s)) _ hBall).
move=>x [hxA hxB].
have hLeft:=hRadiusA _ hxA; have hRight:=hRadiusB _ hxB.
rewrite metric_sym inner_metric_distanceE subr0 in hLeft.
rewrite metric_sym inner_metric_distanceE subr0 in hRight.
change (is_true (mdist (0:X) x<=r+s)); rewrite metric_sym inner_metric_distanceE subr0.
apply:le_trans (euclidean_block_norm_triangle x) _.
exact (lerD hLeft hRight).
Qed.

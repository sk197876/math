(** Federer (1969), 3.2.35, p. 272:
    every original positive distance level of
    a bounded convex body is its actual
    rectifiable tube boundary with Cauchy mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP EuclideanDistanceTubeBasic EuclideanDistanceTubeConvex EuclideanDistanceTubeBoundary
  EuclideanOpenConvexBoundary ConvexBodyCauchy RectifiableSetUP HausdorffMeasure IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_distance_level_cauchy]: the
    Cauchy substitution for H^(n-1)(f^-1{t})
    in the first two equalities of Federer's
    Steiner induction, 3.2.35, p. 272.
    The actual positive tube is nonempty,
    bounded, open and convex, and its whole
    boundary is exactly the original distance
    level. Genuine finite rectifiability and the
    full Cauchy formula therefore apply with
    every original hypothesis discharged. *)
Theorem convex_distance_level_cauchy (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d (t:R):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->0<t ->
  is_m_rectifiable k [set x|d x=t] /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k [set x|d x=t]=
    ((2:R)%:E*@integral_geometric_gauge R k.+1 k (leqnSn k) 1 [set x|(d x<t)%R])%E.
Proof.
move=>hNonempty hS hBound hD ht.
pose T:set (inner_metric_space (@euclidean_inner_productP R k.+1)):=[set x|(d x<t)%R].
have hTNonempty:T!=set0:=@euclidean_distance_tube_nonempty R k.+1 S d t hNonempty hD ht.
have hTOpen:open T:=@euclidean_distance_tube_open R k.+1 S d t hD.
have hTConvex:is_inner_convex T:=@euclidean_distance_tube_convex R k.+1 S d t hD hS.
have hTBound:metric_set_bounded T:=@euclidean_distance_tube_bounded R k.+1 S d t hNonempty hD hBound ht.
have hBoundary:closure T `\` interior T=[set x|d x=t].
  exact:(@euclidean_distance_tube_boundary R k.+1 S d t hNonempty hD ht).
have hRect:=@euclidean_open_convex_boundary_rectifiable R k.+1 T hTNonempty hTOpen hTConvex hTBound.
have hCauchy:=@convex_body_cauchy_formula R k T hTNonempty hTOpen hTConvex hTBound.
rewrite subn1 /= hBoundary in hRect.
rewrite hBoundary in hCauchy.
by split.
Qed.

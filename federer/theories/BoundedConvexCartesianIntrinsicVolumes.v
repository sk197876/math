(** Federer (1969), 3.2.36, pp. 272--273: restore the
    arbitrary original bounded convex factors after the compact proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  InnerConvexNeighbourhoods EuclideanCartesianMap EuclideanCartesianBorel EuclideanCartesianConvexGeometry
  CompactHausdorffMetric CompactSetDistanceProfile CompactMetricBounded MetricBoundedClosureLaws
  CoveringFamilyUP IntegralGeometricGauge ConvexProjectedClosureVolume SteinerTubePolynomial
  CompactConvexCartesianIntrinsicVolumes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_nonempty_cartesian_bounded]: boundedness
    of the original Cartesian body in Federer 3.2.36, p. 272.
    Compact factor closures give a compact nonempty product containing
    the original body; diameter monotonicity proves its boundedness.
    Neither original factor is assumed Borel or closed. *)
Lemma euclidean_nonempty_cartesian_bounded (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  A!=set0 ->B!=set0 ->metric_set_bounded A ->metric_set_bounded B ->
  @metric_set_bounded R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (euclidean_cartesian_set A B).
Proof.
move=>[a ha] [b hb] hA hB.
have hAN:closure A!=set0 by exists a; exact:subset_closure ha.
have hBN:closure B!=set0 by exists b; exact:subset_closure hb.
pose S:set (inner_metric_space (@euclidean_inner_productP R (m+n))):=
  euclidean_cartesian_set (closure A) (closure B).
have hCompact:compact S:=euclidean_cartesian_compact
  (euclidean_bounded_closure_compact hA) (euclidean_bounded_closure_compact hB).
have hNonempty:S!=set0:=euclidean_cartesian_nonempty hAN hBN.
pose C:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R (m+n))):=
  exist _ S (mem_set (conj hCompact hNonempty)).
apply:(metric_bounded_subset _ (compact_metric_diameter_finite C)).
move=>z [hzA hzB]; split; exact:subset_closure.
Qed.

(** Source for [bounded_convex_cartesian_intrinsic_volumes]: the full
    product convolution of Federer 3.2.36, pp. 272--273, for the
    original nonempty bounded convex factors. Exact Cartesian closure
    and the already proved all-set intrinsic closure law transfer the
    compact calculation back to every original coefficient. No source
    measurability, full-dimensionality or positive mass is added;
    every natural coordinate block and degree is retained. *)
Theorem bounded_convex_cartesian_intrinsic_volumes (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  A!=set0 ->B!=set0 ->is_inner_convex A ->is_inner_convex B ->
  metric_set_bounded A ->metric_set_bounded B ->
  forall l:'I_(m+n).+1,
    @integral_geometric_gauge R (m+n) l (steiner_dimension_guard l) 1
      (euclidean_cartesian_set A B)=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N)
      @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A*
      @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B.
Proof.
move=>hAN hBN hA hB hABound hBBound.
have hAC:compact (closure A):=euclidean_bounded_closure_compact hABound.
have hBC:compact (closure B):=euclidean_bounded_closure_compact hBBound.
have hACN:closure A!=set0.
  have [a ha]:=hAN; exists a; exact:subset_closure ha.
have hBCN:closure B!=set0.
  have [b hb]:=hBN; exists b; exact:subset_closure hb.
pose CA:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)):=
  exist _ (closure A) (mem_set (conj hAC hACN)).
pose CB:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)):=
  exist _ (closure B) (mem_set (conj hBC hBCN)).
have hCA:is_inner_convex (val CA):=@inner_convex_closure R (R_n R m) _ (@euclidean_inner_productP R m) A hA.
have hCB:is_inner_convex (val CB):=@inner_convex_closure R (R_n R n) _ (@euclidean_inner_productP R n) B hB.
have hProductN:=euclidean_cartesian_nonempty hAN hBN.
have hProductConvex:=euclidean_cartesian_convex hA hB.
have hProductBound:=euclidean_nonempty_cartesian_bounded hAN hBN hABound hBBound.
move=>l.
rewrite -(@convex_integral_geometric_gauge_closure R (m+n) l (steiner_dimension_guard l) 1
  (euclidean_cartesian_set A B) hProductN hProductConvex hProductBound) euclidean_cartesian_closure.
have hCompact:=@compact_convex_cartesian_intrinsic_volumes R m n CA CB hCA hCB l.
rewrite hCompact; apply:eq_bigr=>i _; apply:eq_bigr=>j _.
by rewrite (@convex_integral_geometric_gauge_closure R m i (steiner_dimension_guard i) 1 A hAN hA hABound)
  (@convex_integral_geometric_gauge_closure R n j (steiner_dimension_guard j) 1 B hBN hB hBBound).
Qed.

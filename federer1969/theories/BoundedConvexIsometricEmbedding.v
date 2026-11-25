(** Federer (1969), 3.2.36, p. 273: the original
    bounded convex body's intrinsic volumes are isometric invariants. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex InnerConvexNeighbourhoods
  CompactHausdorffMetric CompactSetDistanceProfile MetricBoundedClosureLaws CoveringFamilyUP MetricDiameter
  MetricIsometricConvexImage MetricIsometricImageGeometry CompactClosureImage
  CompactConvexIsometricEmbedding IntegralGeometricGauge ConvexProjectedClosureVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_convex_isometric_embedding_intrinsic_volume]:
    the full intrinsic-volume invariance assertion about isometric
    injections in Federer 3.2.36, p. 273. Actual diameter and
    convexity preservation prove the original image hypotheses. Compact
    closure commutes exactly with this continuous image; the proved
    compact theorem and all-set intrinsic closure laws then restore
    both original sources. Arbitrary nonmeasurable and lower-dimensional
    sources, degree zero and all natural ambient blocks remain. *)
Theorem bounded_convex_isometric_embedding_intrinsic_volume (R:realType) m n k
    (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  A!=set0 ->is_inner_convex A ->metric_set_bounded A ->
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  @integral_geometric_gauge R n k hkn 1 (f @` A)=
    @integral_geometric_gauge R m k hkm 1 A.
Proof.
move=>hAN hA hBound hMetric.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hImageN:f @` A!=set0.
  have [a ha]:=hAN; exists (f a); by exists a.
have hImageConvex:is_inner_convex (f @` A).
  exact:(@metric_isometric_convex_image R (R_n R m) (R_n R n) _ _
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f A hMetric hA).
have hImageBound:metric_set_bounded (f @` A).
  by rewrite /metric_set_bounded (@metric_isometric_image_diameter R X Y f hMetric).
have hCompact:compact (closure A):=euclidean_bounded_closure_compact hBound.
have hCN:closure A!=set0.
  have [a ha]:=hAN; exists a; exact:subset_closure ha.
pose C:compact_hausdorff_space X:=exist _ (closure A) (mem_set (conj hCompact hCN)).
have hCConvex:is_inner_convex (val C).
  exact:(@inner_convex_closure R (R_n R m) _ (@euclidean_inner_productP R m) A hA).
have hImageClosure:=@continuous_compact_closure_image R X Y f A
  (metric_isometric_map_continuous hMetric) hCompact.
have hInvariant:=@compact_convex_isometric_embedding_intrinsic_volume R m n k hkm hkn C f hCConvex hMetric.
rewrite -(@convex_integral_geometric_gauge_closure R n k hkn 1 (f @` A)
  hImageN hImageConvex hImageBound) -hImageClosure hInvariant.
exact:(@convex_integral_geometric_gauge_closure R m k hkm 1 A hAN hA hBound).
Qed.

(** Federer (1969), 3.2.36, p. 273: discharge the
    actual closed-convex-generator hypotheses for both Q_1 cover transports. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  ProjectionMeasureUP IntegralGeometricGauge IntegralGeometricGaugeEmpty IntegralGeometricGaugeSubsetOrder
  BoundedConvexIsometricEmbedding MetricIsometricConvexImage MetricIsometricSegments
  MetricIsometricImageGeometry MetricIsometricPreimageDiameter MetricBoundedClosureLaws CoveringFamilyUP
  MetricDiameter TopologicalBorel BorelClosedProjection SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [isometric_closed_convex_generator_image]: the forward
    closed-convex-cover transport in Federer 3.2.36, p. 273.
    At finite cutoffs the original closed generator is compact, so
    its actual isometric image is closed and convex. Diameter and
    actual intrinsic-volume cost are preserved; empty generators have
    their separately proved zero cost, including degree zero. Every
    witness is local and specified by its exact carrier law. *)
Lemma isometric_closed_convex_generator_image (R:realType) m n k
    (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->inner_metric_space (@euclidean_inner_productP R n)):
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  forall j:closed_convex_euclidean_sets R m,metric_set_bounded (val j) ->
  exists q:closed_convex_euclidean_sets R n,
    val q=f @` val j /\extended_metric_diameter (val q)=extended_metric_diameter (val j) /\
    @integral_geometric_gauge R n k hkn 1 (val q)=@integral_geometric_gauge R m k hkm 1 (val j).
Proof.
move=>hMetric j hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hF:=metric_isometric_map_continuous hMetric.
have hCompact:@compact X (val j).
  have h:=euclidean_bounded_closure_compact hBound.
  rewrite -(proj1 (closure_id (val j)) (set_valP j).1) in h; exact h.
have hImageCompact:@compact Y (f @` val j):=continuous_compact (continuous_subspaceT hF) hCompact.
have hClosed:@closed Y (f @` val j):=compact_closed (@metric_hausdorff R Y) hImageCompact.
have hConvex:is_inner_convex (f @` val j).
  exact:(@metric_isometric_convex_image R (R_n R m) (R_n R n) _ _
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f (val j) hMetric (set_valP j).2).
pose q:closed_convex_euclidean_sets R n:=exist _ (f @` val j) (mem_set (conj hClosed hConvex)).
exists q; split; first reflexivity.
split; first exact:(@metric_isometric_image_diameter R X Y f hMetric (val j)).
case:(pselect (val j!=set0))=>hNonempty.
- exact:(@bounded_convex_isometric_embedding_intrinsic_volume R m n k hkm hkn (val j) f
    hNonempty (set_valP j).2 hBound hMetric).
- have hEmpty:val j=set0.
    apply/seteqP; split=>x; last by move=>[].
    move=>hx; exfalso; apply:hNonempty; by exists x.
  change (@integral_geometric_gauge R n k hkn 1 (f @` val j)=
    @integral_geometric_gauge R m k hkm 1 (val j)).
  by rewrite hEmpty image_set0 !integral_geometric_gauge_empty.
Qed.

(** Source for [isometric_closed_convex_generator_preimage]: the reverse
    closed-cover transport in Federer 3.2.36, p. 273. The
    original preimage is closed by actual continuity, convex by the
    proved segment identity and bounded by its actual diameter bound.
    Isometric intrinsic-volume invariance and inclusion of its actual
    image in the target generator prove the cost inequality. Empty
    preimages remain an explicit zero-cover branch. No source-set
    measurability, chosen global inverse or extra cost premise is added. *)
Lemma isometric_closed_convex_generator_preimage (R:realType) m n k
    (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->inner_metric_space (@euclidean_inner_productP R n)):
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  forall q:closed_convex_euclidean_sets R n,metric_set_bounded (val q) ->
    f @^-1` val q=set0 \/exists j:closed_convex_euclidean_sets R m,
      val j=f @^-1` val q /\extended_metric_diameter (val j)<=extended_metric_diameter (val q) /\
      @integral_geometric_gauge R m k hkm 1 (val j)<=@integral_geometric_gauge R n k hkn 1 (val q).
Proof.
move=>hMetric q hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set X:=f @^-1` val q.
case:(pselect (A!=set0))=>hNonempty.
- right.
  have hClosed:@closed X A.
    have hF:continuous (f:X->Y):=@metric_isometric_map_continuous R X Y f hMetric.
    exact:((@continuous_closedP X Y f).1 hF _ (set_valP q).1).
  have hConvex:is_inner_convex A.
    exact:(@metric_isometric_convex_preimage R (R_n R m) (R_n R n) _ _
      (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f (val q) hMetric (set_valP q).2).
  have hDiameter:=@metric_isometric_preimage_diameter R X Y f hMetric (val q).
  have hABound:metric_set_bounded A:=le_lt_trans hDiameter hBound.
  pose j:closed_convex_euclidean_sets R m:=exist _ A (mem_set (conj hClosed hConvex)).
  exists j; split; first reflexivity.
  split; first exact:hDiameter.
  rewrite -(@bounded_convex_isometric_embedding_intrinsic_volume R m n k hkm hkn A f
    hNonempty hConvex hABound hMetric).
  have hImageCompact:@compact Y (f @` A).
    have hCompact:@compact X A.
      have h:=euclidean_bounded_closure_compact hABound; by rewrite -(proj1 (closure_id A) hClosed) in h.
    exact:continuous_compact (continuous_subspaceT (metric_isometric_map_continuous hMetric)) hCompact.
  apply:integral_geometric_gauge_subset_order.
  + exact:lexx.
  + apply:metric_borel_suslin; apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R Y) hImageCompact.
  + apply:metric_borel_suslin; exact:closed_borel_set (set_valP q).1.
  + by move=>y [x hx <-].
- left; apply/seteqP; split=>x; last by move=>[].
  move=>hx; exfalso; apply:hNonempty; by exists x.
Qed.

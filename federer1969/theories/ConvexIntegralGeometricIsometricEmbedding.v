(** Federer (1969), 3.2.36, p. 273: Q_1 is
    invariant under arbitrary actual Euclidean isometric injections. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  ProjectionMeasureUP IntegralGeometricGauge IntegralGeometricMeasureUP IntegralGeometricMeasure
  IntegralGeometricClosedCovers IsometricConvexCoverGenerators CaratheodoryFiniteGeneratorTransport
  MetricDiameter TopologicalBorel BorelClosedProjection SuslinSetUP CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_isometric_embedding]: the
    final measure assertion of Federer 3.2.36, p. 273: Q_1
    is unchanged by isometric injections. The subscript is one.
    Both directions use the proved actual closed-convex construction;
    finite cutoff generators have proved local image or preimage
    witnesses with their actual diameter and cost bounds. Empty
    preimages contribute zero explicitly. Arbitrary original target
    sets, infinite values and all admissible natural degrees remain;
    no measurability, boundedness, selected inverse or covering premise
    is imposed on the original A. *)
Theorem convex_integral_geometric_isometric_embedding (R:realType) m n k
    (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->inner_metric_space (@euclidean_inner_productP R n)):
  (forall x y,mdist (f x) (f y)=mdist x y) ->forall A,
    @convex_integral_geometric_measure R n k hkn 1 (f @` A)=
    @convex_integral_geometric_measure R m k hkm 1 A.
Proof.
move=>hMetric.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose J:=closed_convex_euclidean_sets R m.
pose K:=closed_convex_euclidean_sets R n.
pose S:=fun j:J=>val j.
pose T:=fun q:K=>val q.
pose c:=fun j:J=>@integral_geometric_gauge R m k hkm 1 (val j).
pose d:=fun q:K=>@integral_geometric_gauge R n k hkn 1 (val q).
pose mu:=@convex_integral_geometric_measure R m k hkm 1.
pose rho:=@convex_integral_geometric_measure R n k hkn 1.
have hMu:=@convex_integral_geometric_closed_cover_specification R m k hkm 1 (lexx 1).
have hRho:=@convex_integral_geometric_closed_cover_specification R n k hkn 1 (lexx 1).
have hC j:0<=c j.
  apply:integral_geometric_gauge_nonnegative; first exact:lexx.
  apply:metric_borel_suslin; exact:closed_borel_set (set_valP j).1.
have hD q:0<=d q.
  apply:integral_geometric_gauge_nonnegative; first exact:lexx.
  apply:metric_borel_suslin; exact:closed_borel_set (set_valP q).1.
have hImage j:metric_set_bounded (S j) ->exists q,
    f @` S j `<=` T q /\extended_metric_diameter (T q)<=extended_metric_diameter (S j) /\d q<=c j.
  move=>hBound; have [q [hCarrier [hDiameter hCost]]]:=
    @isometric_closed_convex_generator_image R m n k hkm hkn f hMetric j hBound.
  exists q; split.
  - rewrite /S /T hCarrier; by move=>y.
  - split; first by rewrite /S /T hDiameter.
    by rewrite /c /d hCost.
have hInjective:injective f.
  move=>x y h; apply:(@mdist_positivity R X x y).
  by rewrite -(hMetric x y) h mdistxx.
have hPreimage q:metric_set_bounded (T q) ->f @^-1` T q=set0 \/exists j,
    f @^-1` T q `<=` S j /\extended_metric_diameter (S j)<=extended_metric_diameter (T q) /\c j<=d q.
  move=>hBound; have [hEmpty|[j [hCarrier [hDiameter hCost]]]]:=
    @isometric_closed_convex_generator_preimage R m n k hkm hkn f hMetric q hBound.
  - by left.
  - right; exists j; split.
    + rewrite /S /T hCarrier; by move=>x.
    + by split.
have hUpper:=@caratheodory_finite_generator_image_bound R X Y J K S T c d f mu rho
  hMu hRho hD hImage.
have hLower:=@caratheodory_finite_generator_preimage_bound R X Y J K S T c d f mu rho
  hMu hRho hC hD hInjective hPreimage.
move=>A; apply/eqP; by rewrite eq_le hUpper hLower.
Qed.

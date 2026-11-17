(** Federer (1969), 3.4.8(6), pp. 328–329:
    the actual prefix coordinates transport null
    direction sets from R^p to the original
    sphere S. No measurability premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct
  AnalyticPrefixCoordinatesUP AnalyticPrefixCoordinateLaws AnalyticPrefixSphereCoordinates
  AnalyticPrefixSphereAction MetricSubsetBackground HausdorffMetricSubset HausdorffMeasure
  HausdorffIsometricEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_sphere_coordinate_null]: the
    exceptional-direction nullity in 3.4.7, p. 324,
    transfers to the original prefix sphere used
    in 3.4.8(6), p. 329. Exact original projection
    and inclusion equations supply the isometry. *)
Theorem analytic_prefix_sphere_coordinate_null (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  p (hPN:(p<=n)%N) (P:Hom X (R_n R p)) (S:Hom (R_n R p) X)
  (hP:is_analytic_prefix_projection omega hPN P) (hS:is_analytic_prefix_section e hPN S)
  (D:set (R_n R p)):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R p)) (p-1)
    [set y|inner_norm (@euclidean_inner_productP R p) y = 1 /\D y] = 0%E ->
  @hausdorff_measure R [the metricType R of metric_subset (@analytic_prefix_unit_sphere R X B hB n e p)]
    (p-1) [set u|D (P (val u))] = 0%E.
Proof.
move=>hNull.
pose XT:=inner_metric_space hB.
pose YT:=inner_metric_space (@euclidean_inner_productP R p).
pose sphere:=@analytic_prefix_unit_sphere R X B hB n e p.
have hCoordinates:=@analytic_prefix_sphere_image R X B hB n e he hON omega hDual p hPN P S hP hS.
have hLeft:cancel S P:=@analytic_prefix_projection_section R X n e omega p hPN P S hDual hP hS.
have hFixed:=@analytic_prefix_section_projection_fixed R X B hB n e he hON omega hDual p hPN P S hP hS.
have hNorm:=@analytic_prefix_section_norm R X B hB n e hON p hPN S hS.
have hDistance (x y:YT):mdist (S x:XT) (S y:XT) = mdist x y.
  rewrite !inner_metric_distanceE.
  change (inner_norm hB (S x-S y) = inner_norm (@euclidean_inner_productP R p) (x-y)).
  have hLinear:S (x-y) = S x-S y:=linearB (hom_as_linear S) x y.
  by rewrite -hLinear hNorm.
rewrite -(@hausdorff_metric_subset_measure R XT sphere (p-1) [set u|D (P (val u))]).
have hImage:(fun u:metric_subset sphere=>(val u:XT)) @` [set u|D (P (val u))] =
  S @` [set y:YT|inner_norm (@euclidean_inner_productP R p) y = 1 /\D y].
  apply/seteqP;split=>x.
  - move=>[u hD <-];have [hUnit hTail]:=set_valP u.
    exists (P (val u));last exact:hFixed.
    split;last exact:hD.
    by rewrite -hNorm (hFixed (val u) hTail).
  - move=>[y [hUnit hD] <-].
    have hSphere:sphere (S y).
      rewrite /sphere -hCoordinates;exists y;by [].
    exists (exist _ (S y) (mem_set hSphere));last by [].
    change (D (P (S y)));by rewrite hLeft.
rewrite hImage (@hausdorff_isometric_embedding_invariance R YT XT S P hLeft hDistance).
exact:hNull.
Qed.

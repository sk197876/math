(** Federer (1969), 3.2.35, pp. 271--272:
    every actual projected volume of a nonempty
    bounded convex source agrees with its closure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionBoundedClosure EuclideanProjectionConvexImage
  EuclideanConvexClosureVolume ProjectedVolumeMeasurability IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convex_projected_closure_volume]:
    supporting the original zeta^m(S) coefficients
    in Steiner's formula, Federer 3.2.35,
    pp. 271--272. Projection of the bounded
    source closure is exactly closure of the
    original projected source. The proved all-set
    convex closure-volume theorem applies there.
    No source measurability or full dimension
    hypothesis is added. *)
Theorem convex_projected_closure_volume (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  projected_volume_function (closure S) p=projected_volume_function S p.
Proof.
move=>hNonempty hS hBound.
have hPNonempty:euclidean_projection_linear p @` S!=set0.
  have [a ha]:=hNonempty; exists (euclidean_projection_linear p a); by exists a.
rewrite /projected_volume_function (@euclidean_projection_bounded_closure R n m p S hBound).
exact:euclidean_convex_closure_volume hPNonempty (euclidean_projection_convex_image hS).
Qed.

(** Source for [convex_integral_geometric_gauge_closure]:
    closing the original bounded convex source
    leaves each intrinsic-volume gauge unchanged,
    supporting Federer 3.2.35, pp. 271--272.
    Every actual projection agrees pointwise before
    the existing opaque exponent norm is used. *)
Theorem convex_integral_geometric_gauge_closure (R:realType) n m (hmn:(m<=n)%N) t
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  @integral_geometric_gauge R n m hmn t (closure S)=@integral_geometric_gauge R n m hmn t S.
Proof.
move=>hNonempty hS hBound.
have he:projected_volume_function (m:=m) (closure S)=projected_volume_function (m:=m) S.
  apply:funext=>p; exact:convex_projected_closure_volume hNonempty hS hBound.
by rewrite /integral_geometric_gauge he.
Qed.

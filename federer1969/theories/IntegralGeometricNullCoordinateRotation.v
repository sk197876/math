(** Federer (1969), 4.1.20, p. 378, first displayed
    proof equation: choose one g in O(n) for which
    L^m[(p_lambda composed with g)(A)] is zero for every
    lambda in Lambda(n,m). Reuse the original coordinate
    projection of 1.7.4, pp. 30–31, and the already proved
    finite-projection null choice; no new Haar construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric ExteriorIndices CoordinateProjection
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalEuclidean
  IntegralGeometricMeasure IntegralGeometricFiniteNullProjections
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integral_geometric_null_coordinate_rotation]:
    the simultaneous coordinate projection equation in the
    proof of Federer 4.1.20, p. 378. The original arbitrary
    set and every finite coordinate selection are retained. *)
Theorem integral_geometric_null_coordinate_rotation (R:realType) n m
    (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @integral_geometric_measure R n m hmn 1 A=0->
  exists g:euclidean_orthogonal_group R n,forall lambda:Lambda n m,
    @euclidean_lebesgue_measure R m
      ((fun x=>@coordinate_projection R n m lambda (orthogonal_element_map g x)) @` A)=0.
Proof.
move=>hNull.
have hProjection lambda:exists q:euclidean_projection_space R n m,
    forall x,euclidean_projection_linear q x=@coordinate_projection R n m lambda x.
  exact:(@euclidean_projection_linear_complete R n m
    (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _)
    (@coordinate_projection_orthogonal R n m lambda)).
pose p lambda:orthogonal_projection_metric_space R n m:=
  sval (constructive_indefinite_description (hProjection lambda)).
have hValue lambda:=svalP (constructive_indefinite_description (hProjection lambda)).
have[g hG]:=@integral_geometric_finite_null_projections R n m hmn
  [the finType of Lambda n m] p A hNull.
exists g=>lambda.
have hMaps:(fun x=>euclidean_projection_linear (p lambda) (orthogonal_element_map g x))=
    (fun x=>@coordinate_projection R n m lambda (orthogonal_element_map g x)).
  apply:funext=>x;exact:(hValue lambda (orthogonal_element_map g x)).
by rewrite -hMaps;exact:hG lambda.
Qed.

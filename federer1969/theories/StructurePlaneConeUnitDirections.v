(** Federer (1969), 3.3.18, p. 301: actual nonempty
    cones and their positive rays in the converse counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanCoordinateMetric FiniteCoordinates
  GrassmannHomogeneousSpace OrthogonalMaps MetricSetDistanceSealed MetricSetDistanceBasic
  StructureCone StructureConeBasic StructureProjectionCone StructureProjectionKernel EuclideanProjectionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_positive_plane_cone_unit_point]: supporting
    the actual false-converse example in Federer 3.3.18, p. 301.
    Any positive-dimensional original plane has an actual unit vector
    inside its original cone of radius two, at EVERY positive aperture.
    An actual orthogonal frame gives the vector; the distance laws
    give distance zero. No cone nonemptiness premise is supplied. *)
Theorem structure_positive_plane_cone_unit_point (R:realType) n k (hk:(0<k)%N)
    (V:G (R_n R n) k) (s:R):
  0<s ->exists u:inner_metric_space (@euclidean_inner_productP R n),
    inner_norm (@euclidean_inner_productP R n) u= 1 /\
    structure_cone V (0%R:inner_metric_space (@euclidean_inner_productP R n)) 2%:E s u.
Proof.
move=>hs.
have [f [hf hRange]]:=@grassmann_orthogonal_frame R (R_n R k) (R_n R n)
  (@euclidean_inner_product R k) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R k) (@euclidean_inner_productP R n)
  k (@coordinate_basis R k) (@coordinate_basisP R k) V.
pose e:=@coordinate_basis R k (Ordinal hk).
pose u:=f e.
have hUnit:inner_norm (@euclidean_inner_productP R n) u= 1.
  rewrite /u (orthogonal_map_norm (@euclidean_inner_productP R k) (@euclidean_inner_productP R n) hf).
  exact:euclidean_coordinate_unit_norm.
have hMember:grassmann_val V u by apply/hRange; exists e.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set X:=[set x|grassmann_val V x].
have hA:A!=set0:=structure_plane_nonempty V.
have hd:=@MetricSetDistance.laws R [the metricType R of X] A hA.
have hDistance:=metric_set_distance_member hd hMember.
exists u; split; first exact:hUnit.
apply/((@structure_cone_specification R n k V 0%R 2%:E s) _ hd u).
rewrite subr0 hDistance hUnit mulr0; split; first exact:ltr01.
by rewrite lte_fin ltr1n.
Qed.

(** Source for [structure_projection_positive_ray_cone]: supporting
    every radial cluster in the original cone for the false-converse
    assertion of Federer 3.3.18, p. 301. Actual linearity and norm
    homogeneity preserve the original strict angular inequality under
    every positive dilation. The radius remains genuinely infinite. *)
Lemma structure_projection_positive_ray_cone (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m)
    (v:inner_metric_space (@euclidean_inner_productP R n)) (s c:R):
  0<c ->structure_cone (structure_projection_kernel hmn p) 0%R +oo s v ->
  structure_cone (structure_projection_kernel hmn p) 0%R +oo s (c *:v).
Proof.
move=>hc hCone.
have [hAngle _]:=(structure_projection_coneE hmn p 0%R +oo s v).1 hCone.
apply/(structure_projection_coneE hmn p 0%R +oo s (c *:v)).
rewrite subr0 linearZ !inner_normZ (ger0_norm (ltW hc)).
split; last exact:ltry.
rewrite mulrCA ltr_pM2l //.
by rewrite subr0 in hAngle.
Qed.

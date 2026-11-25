(** Federer (1969), 4.1.24, p. 381: the
    original Lipschitz images of integral polyhedral
    zero-currents remain integral polyhedral zero-currents.
    The zero-simplex is the actual Dirac current;
    the least additive-subgroup laws retain every
    signed integer combination. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerConvex ConvexHull LipschitzUP SmoothCompactSet CurrentSpaces CurrentDirac
  FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  GeneratedAdditiveSubgroupUP PolyhedralCurrentGenerators PolyhedralCurrentAlgebra
  PolyhedralCurrentFlat FlatCurrentImageSubgroup CurrentFlatDiracPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integral_polyhedral_dirac_in_index]: every
    point in the original K gives its actual
    integral zero-simplex in P-script_(0,K), as used
    for the zero-degree assertion of 4.1.24, p. 381. *)
Theorem integral_polyhedral_dirac_in_index (R:realType)
    (h2:(1+1:R)!=0) n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (c:R_n R n):
  smooth_compact_carrier K c->
  @integral_polyhedral_current_class R h2 n 0%N U hU K
    (@dirac_current R h2 n U hU c).
Proof.
move=>hc;pose v:=fun _:'I_1=>c.
have hSingleton:@is_inner_convex R (R_n R n) [set c].
  move=>x y -> -> t ht ht1.
  by rewrite -scalerDl subrK scale1r.
have hHull:@polyhedral_simplex_vertex_hull R n 0%N v `<=` smooth_compact_carrier K.
  move=>x hx;have hxc:[set c] x.
    apply:(@convex_hull_least R (R_n R n)
      [set y|exists i:'I_1,v i=y] [set c] _ hSingleton x hx).
    by move=>y [i <-].
  by move:hxc=>->.
have hPoly:=@integral_polyhedral_current_generator R h2 n 0%N U hU K v hHull.
by rewrite open_oriented_simplex_point in hPoly.
Qed.

(** Source for [integral_polyhedral_zero_lipschitz_pushforward]:
    every defining image in degree zero is still
    in the original same-index integral polyhedral class,
    Federer 4.1.24, p. 381. The source dimension
    is arbitrary. No convexity of either compact
    or positive ambient dimension is required. *)
Theorem integral_polyhedral_zero_lipschitz_pushforward
    (R:realType) (h2:(1+1:R)!=0) d n
    (Z:set (R_n R d)) (U:set (R_n R n))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f:R_n R d->R_n R n) (hImage:forall x,Z x->U (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f)
    (C:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hCK:forall x,smooth_compact_carrier C x->smooth_compact_carrier K (f x))
    (P:@current_space R h2 d Z hZ 0%N)
    (hP:@integral_polyhedral_current_class R h2 d 0%N Z hZ C P)
    (hFlat:@is_flat_current R h2 d 0%N Z hZ P):
  @integral_polyhedral_current_class R h2 n 0%N U hU K
    (@CurrentFlatLipschitzPushforward.value R h2 d n 0%N Z U hZ hU
      f hImage hLocal P hFlat).
Proof.
pose Source:=@current_space R h2 d Z hZ 0%N.
pose Target:=@current_space R h2 n U hU 0%N.
pose Flat:=@is_flat_current R h2 d 0%N Z hZ.
pose Poly:=@integral_polyhedral_current_class R h2 n 0%N U hU K.
pose Push:=@CurrentFlatLipschitzPushforward.value R h2 d n 0%N Z U hZ hU
  f hImage hLocal.
pose Good:set Source:=[set T|exists hT:Flat T,Poly (Push T hT)].
have hGood:is_subgroup (fun T S:Source=>T+S) (fun T=>-T) 0 Good.
  exact:(@flat_current_image_subgroup R h2 d n 0%N Z U hZ hU f hImage hLocal
    Poly (@integral_polyhedral_current_subgroup R h2 n 0%N U hU K)).
have hGenerators:@polyhedral_simplex_generators R h2 d 0%N Z hZ C `<=` Good.
  move=>T [v [hHull <-]];rewrite open_oriented_simplex_point.
  pose c:=v ord0.
  have hc:=@polyhedral_simplex_vertices_in_index R d 0%N Z C v hHull ord0.
  have hPointPoly:@integral_polyhedral_current_class R h2 d 0%N Z hZ C
      (@dirac_current R h2 d Z hZ c).
    exact:integral_polyhedral_dirac_in_index hc.1.
  pose hPointFlat:Flat (@dirac_current R h2 d Z hZ c):=
    ex_intro _ C (@integral_polyhedral_current_flat_supported
      R h2 d 0%N Z hZ C (@dirac_current R h2 d Z hZ c) hPointPoly).
  exists hPointFlat.
  rewrite /Push (@current_flat_lipschitz_dirac_pushforward
    R h2 d n Z U hZ hU f hImage hLocal c hc.2 hPointFlat).
  exact:integral_polyhedral_dirac_in_index (@hCK c hc.1).
have[hWitness hImagePoly]:=generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 d 0%N Z hZ C)
  hGood hGenerators hP.
have hValue:=@current_flat_lipschitz_pushforward_proof_independent
  R h2 d n 0%N Z U hZ hU f hImage hLocal P hWitness hFlat.
by rewrite -hValue.
Qed.

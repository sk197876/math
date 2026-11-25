(** Federer (1969), 3.2.38, p. 275: the exact top intrinsic
    coefficient of the actual affine image, including singular maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  OrthogonalMaps PolarFactorisationUP EuclideanLinearIntrinsicFactor EuclideanAffineImageGeometry
  EuclideanLinearMaps EuclideanLinearJacobian EuclideanLebesgueDimensions EuclideanLebesgueDeterminant
  CompactHausdorffMetric CompactSetDistanceProfile CompactConvexIsometricEmbedding
  IntegralGeometricGauge FullDimensionIntegralGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_convex_top_intrinsic_volume]: the equality
    zeta^m(g(K))=J_m f(a)L^m(K) in Federer 3.2.38, p. 275,
    proved for every nonempty compact convex original source. The
    actual all-rank polar factor gives a square source map followed
    by an affine isometric injection. Intrinsic invariance from
    3.2.36, full-dimensional gauge equality and the determinant image
    law prove the identity, including rank-deficient maps and m=0. *)
Theorem affine_convex_top_intrinsic_volume (R:realType) m n (hmn:(m<=n)%N)
    (D:Hom (R_n R m) (R_n R n)) (a:R_n R m) (b:R_n R n)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m))):
  Q!=set0 ->compact Q ->is_inner_convex Q ->
  @integral_geometric_gauge R n m hmn 1 ((fun x=>b+D (x-a)) @` Q)=
    ((euclidean_linear_jacobian m D)%:E*@euclidean_lebesgue_measure R m Q)%E.
Proof.
move=>hNonempty hCompact hConvex.
have [K [O [hFactor hJacobian]]]:=euclidean_linear_intrinsic_factor_exists D hmn.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set X:=(fun x:X=>0+hom_of_linear K x) @` Q.
have hAN:A!=set0 by have [x hx]:=hNonempty; exists (K x); exists x=>//; by rewrite add0r.
have hAC:compact A:=@euclidean_affine_hom_compact_image R m m (hom_of_linear K) 0 Q hCompact.
have hAV:is_inner_convex A:=@affine_hom_convex_image R (R_n R m) (R_n R m) (hom_of_linear K) 0 Q hConvex.
have hAS:A=(K:X->X) @` Q by apply/seteqP; split=>y [x hx <-]; exists x=>//; by rewrite add0r.
pose C:compact_hausdorff_space X:=exist _ A (mem_set (conj hAC hAN)).
pose c:Y:=b-D a.
pose F:X->Y:=fun z=>c+O z.
have hMetric x y:mdist (F x) (F y)=mdist x y.
  rewrite !inner_metric_distanceE.
  have hDifference:F x-F y=O (x-y).
    by rewrite /F opprD addrACA subrr add0r linearB.
  rewrite hDifference; exact:(orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (injection_factor_orthogonal hFactor) (x-y)).
have hPoint x:F (K x)=b+D (x-a).
  by rewrite /F (injection_factor_equation hFactor) hom_as_linearE /c linearB addrAC addrA.
have hImage:((fun x:X=>b+D (x-a)) @` Q)=F @` A.
  rewrite hAS; apply/seteqP; split=>y.
  - move=>[x hx <-]; exists (K x); first by exists x.
    by rewrite hPoint.
  - move=>[z [x hx <-] <-]; rewrite hPoint; by exists x.
rewrite hImage (@compact_convex_isometric_embedding_intrinsic_volume R m n m
  (leqnn m) hmn C F hAV hMetric)
  (@equal_dimension_integral_geometric_gauge R m (leqnn m) 1 A (lexx 1))
  hAS euclidean_lebesgue_linear_image hJacobian.
reflexivity.
Qed.

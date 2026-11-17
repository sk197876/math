(** Actual coordinate stretching for the section comparison
    in Federer (1969), 3.2.45,
    pp. 279–280. The prescribed
    diagonal maps are those of 2.7.16(1),
    p. 135, and reflections those
    of 2.10.30, p. 195. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  CoordinateProjection OrthonormalFamilies UnitNormalGeometry EuclideanLinearMaps IntegralGeometricGauge
  ReflectionStretchCoefficients ConvexWeightedReflectionIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_stretch_reflection]:
    supporting linear-map connection for the
    coefficient comparison in Federer 3.2.45,
    pp. 279–280. The actual
    diagonal map scaling coordinate i by
    t is a weighted combination of
    the identity and the original reflection
    in that coordinate. The scalar weights
    are proved independently; no volume formula
    forms part of this identity. Other
    coordinates are fixed. Every real t
    is allowed, including zero. *)
Lemma euclidean_coordinate_stretch_reflection (R : realType) n (i : 'I_n) (t : R) :
  forall x : R_n R n,
    @euclidean_diagonal_map R n (fun j => if j==i then t else 1%R) x=
      ((1+t)/2)*:x+((1-t)/2)*:
        normal_reflection (@euclidean_inner_productP R n) (@coordinate_basis R n i) x.
Proof.
pose a := ((1+t)/2)%R; pose b := ((1-t)/2)%R.
have [hSum [hCoefficient hAbs]] := @reflection_stretch_coefficients R t.
have hDifference : a-b=t by rewrite /a /b; field; by rewrite ?pnatr_eq0.
move=> x; apply/ffunP=> j.
rewrite /euclidean_diagonal_map /euclidean_diagonal /normal_reflection !ffunE
  inner_coordinateE euclidean_inner_basis /coordinate_basis ?ffunE.
case: (eqVneq j i)=> [->|hNe].
- change (t*x i=a*x i+b*(x i-2*x i*1)).
  rewrite mulr1.
  have hFactor : a*x i+b*(x i-2*x i)=(a-b)*x i by ring.
  by rewrite hFactor hDifference.
- change (1*x j=a*x j+b*(x j-2*x i*0)).
  by rewrite mulr0 subr0 -mulrDl hSum.
Qed.

(** Source for [convex_coordinate_stretch_intrinsic_volume]:
    supporting one-coordinate intrinsic-volume bound for
    the original section comparison in Federer
    3.2.45, pp. 279–280.
    Stretching one actual coordinate by t>=1
    increases every intrinsic coefficient by at
    most t. Apply the proved weighted
    reflection average to the actual diagonal
    map and the standard unit normal;
    its absolute-weight sum is exactly t.
    Compact convex sources may be thin,
    and degree zero is retained. *)
Theorem convex_coordinate_stretch_intrinsic_volume (R : realType) n k (hKN : (k<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (i : 'I_n) (t : R) :
  K !=set0 -> compact K -> is_inner_convex K -> (1<=t)%R ->
  (@integral_geometric_gauge R n k hKN 1
    ((@euclidean_diagonal_map R n (fun j => if j==i then t else 1%R)) @` K) <=
    t%:E*@integral_geometric_gauge R n k hKN 1 K)%E.
Proof.
move=> hNonempty hCompact hConvex hT.
pose a := ((1+t)/2)%R; pose b := ((1-t)/2)%R.
pose u := @coordinate_basis R n i.
have hUnit : euclidean_inner_product u u= 1.
  by rewrite euclidean_inner_basis /u /coordinate_basis ffunE eqxx.
have [hSum [hCoefficient hAbs]] := @reflection_stretch_coefficients R t.
have h := @convex_weighted_reflection_intrinsic_volume R n k hKN K u a b
  (@euclidean_diagonal_map R n (fun j => if j==i then t else 1%R))
  hNonempty hCompact hConvex hUnit hSum (@euclidean_coordinate_stretch_reflection R n i t).
by rewrite (hAbs hT) in h.
Qed.

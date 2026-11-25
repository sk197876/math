(** Federer (1969), 4.1.11, p. 365: the two-point
    join is the original oriented segment. Its ambient
    affine parameter map is a member of the existing
    opaque affine-map space of 2.7.16, pp. 133–134.
    Only that space's public evaluation laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom AffineMaps AffineMapSpaceUP AffineMapSpaceSealed RealNormUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialLocal
  NormHigherCurveDerivativeUP NormFiniteLinearBound NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanScalarCoordinateMaps EuclideanAffineSmooth ConvexMetricSegment CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSegmentAffineMap.
Variable R:realType.
Variable n:nat.
Local Notation Line := (R_n R 1%N).
Local Notation X := (R_n R n).
Local Notation NL := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNL := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables u v:X.

(** Source for [current_segment_affine_linear]: the
    original constant linear velocity map z mapped to
    z_1(v-u), supporting the segment identity in Federer
    4.1.11, p. 365. This composes the existing coordinate
    and scalar-multiplication linear maps. *)
Definition current_segment_affine_linear:Hom Line X:=
  hom_comp (@scalar_coefficient_linear_map R X (v-u))
    (@euclidean_scalar_coordinate_map R 1%N ord0).

(** Source for [current_segment_affine_map]: the original
    affine parameter map with offset u and velocity v-u,
    supporting Federer 4.1.11, p. 365. Its member is
    supplied by the existing affine-space inverse law;
    no representation of that opaque space is opened. *)
Definition current_segment_affine_map:Line->X:=
  @affine_map_eval R Line X
    (@affine_space_iso_inv R Line X (affine_maps Line X)
      (@affine_map_eval R Line X) (@affine_mapsP R Line X)
      (current_segment_affine_linear,u)).

(** Source for [current_segment_affine_linear_values]:
    the original parameter differential has the exact
    coordinate value, supporting Federer 4.1.11, p. 365. *)
Lemma current_segment_affine_linear_values z:
  current_segment_affine_linear z=(@euclidean_one_project R z)*:(v-u).
Proof. by rewrite /current_segment_affine_linear hom_compE. Qed.

(** Source for [current_segment_affine_map_values]: the
    original parameter map is u+t(v-u), supporting the
    segment identity in Federer 4.1.11, p. 365, with
    the literal path of 4.1.8, p. 362. *)
Lemma current_segment_affine_map_values z:
  current_segment_affine_map z=u+current_segment_affine_linear z.
Proof. by rewrite /current_segment_affine_map affine_space_iso_invE. Qed.

(** Source for [current_segment_affine_map_scalar_values]:
    the ambient parameter map agrees with the original
    affine segment at every real parameter, supporting
    Federer 4.1.11, p. 365. *)
Lemma current_segment_affine_map_scalar_values t:
  current_segment_affine_map (@euclidean_one_embed R t)=metric_segment_point u v t.
Proof.
by rewrite current_segment_affine_map_values current_segment_affine_linear_values euclidean_one_embedK.
Qed.

(** Source for [current_segment_affine_map_affine]: the
    original parameter map is affine, supporting the affine
    and segment identities in Federer 4.1.11, p. 365. *)
Lemma current_segment_affine_map_affine:is_affine_map current_segment_affine_map.
Proof. exact:(affine_space_eval_affine (@affine_mapsP R Line X) _). Qed.

(** Source for [current_segment_affine_map_smooth]: the
    original affine segment map is smooth on every given
    open parameter domain, supporting Federer 4.1.11,
    p. 365. Zero velocity and target dimension remain allowed. *)
Theorem current_segment_affine_map_smooth (U:set Line)
    (hU:forall z,U z->norm_domain_interior NL U z):
  norm_class_all_orders hNL hNX U current_segment_affine_map.
Proof. exact:(euclidean_affine_map_smooth hU current_segment_affine_map_affine). Qed.

(** Source for [current_segment_affine_map_differential]:
    the actual original differential is the constant
    velocity map, supporting the interval-integral proof
    of the segment identity in Federer 4.1.11, p. 365. *)
Theorem current_segment_affine_map_differential (U:set Line)
    (hU:forall z,U z->norm_domain_interior NL U z) z:
  U z->@current_map_differential R 1%N n U current_segment_affine_map z=current_segment_affine_linear.
Proof.
move=>hz;apply:current_map_differential_unique.
have hBound:=@norm_finite_linear_bounded R Line X NL NX hNL hNX 1%N
  (@coordinate_basis R 1%N) (@coordinate_basisP R 1%N) current_segment_affine_linear.
have hConstant:=@norm_differential_constant R Line X NL NX hNL hNX U z u (hU z hz).
have hLinear:=@norm_differential_linear R Line X NL NX hNL hNX U z current_segment_affine_linear
  (hU z hz) hBound.
have hSum:=@norm_differential_add R Line X NL NX hNX U (fun _=>u)
  current_segment_affine_linear z 0 current_segment_affine_linear hConstant hLinear.
rewrite add0r in hSum.
apply:(@norm_differential_domain_agreement R Line X NL NX hNL U _
  current_segment_affine_map z current_segment_affine_linear _ hSum)=>t _.
exact:esym (current_segment_affine_map_values t).
Qed.
End CurrentSegmentAffineMap.

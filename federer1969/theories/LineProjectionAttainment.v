(** Supporting degree-one projection for Federer (1969), 2.10.4, p. 172,
    final observation. The adjoint of an isometric line frame parallel to a
    nonzero vector preserves that vector's norm. This is the vector case of
    1.7.7, p. 34, obtained directly from the normalization, frame and
    adjoint laws. Source context for these algebraic ingredients:
    OrthonormalFrameMap.v and ProjectionNorm.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormalization OrthonormalFamilies OrthogonalMaps OrthonormalFrameMap
  CoordinateProjection Adjoint AdjointUP AdjointCriteria.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [line_projection_preserves_vector_norm]:
    supporting extremal projection for the degree-one
    diameter identity of Federer 2.10.4, p. 172.
    The vector is nonzero; no separate ambient-dimension
    hypothesis or assumed maximizing projection is needed. *)
Theorem line_projection_preserves_vector_norm (R : realType) (n : nat) (v : R_n R n) :
  v!=0 -> exists p : {linear R_n R n -> R_n R 1}, O_star p /\
    inner_norm (@euclidean_inner_productP R 1) (p v)=inner_norm (@euclidean_inner_productP R n) v.
Proof.
move=> hv.
pose e (_ : 'I_1) := inner_normalize (@euclidean_inner_productP R n) v.
have he : orthonormal_family (@euclidean_inner_product R n) e.
  move=> i j; rewrite (ord1 i) (ord1 j) eqxx.
  exact: inner_normalize_square hv.
have [f [hf hfe]] := @orthonormal_frame_map_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) 1 e he.
pose p := inner_adjoint (@euclidean_inner_productP R 1) (@euclidean_inner_productP R n)
  (@coordinate_basisP R 1) f.
have hadj : is_adjoint (@euclidean_inner_product R 1) (@euclidean_inner_product R n) f p :=
  inner_adjointP _ _ _ f.
have hcan := (@orthogonal_iff_adjoint_left_inverse R (R_n R 1) (R_n R n)
  (@euclidean_inner_product R 1) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R 1) f p hadj).1 hf.
pose w := inner_norm (@euclidean_inner_productP R n) v*: (@coordinate_basis R 1 ord0).
have hfw : f w=v.
  rewrite /w linearZ hfe /e; exact: inner_normalizeK hv.
exists p; split; first by exists f; split.
have hpv : p v=w by rewrite -hfw hcan.
have hh := @orthogonal_map_norm R (R_n R 1) (R_n R n)
  (@euclidean_inner_product R 1) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R 1) (@euclidean_inner_productP R n) f hf w.
by rewrite hfw in hh; rewrite hpv.
Qed.

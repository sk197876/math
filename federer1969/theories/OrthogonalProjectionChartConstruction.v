(** Private existence proof of the orthogonal coordinates supporting Fubini
    in Federer (1969), 2.10.46, p. 203. Carry the adjoint frame of the
    supplied projection to that of the second-coordinate projection by an
    orthogonal automorphism, and take its inverse. The existing
    frame-extension proof of 1.7.3, pp. 29–30, supplies the automorphism
    through orthogonal_injection_transitive. Downstream users receive only
    the opaque chart laws. Source context: EuclideanRightBlockProjection.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  CoordinateProjection OrthogonalMaps OrthogonalFinite OrthogonalInjectionSpaces
  AdjointUP AdjointLaws EuclideanRightBlockProjection OrthogonalProjectionChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthogonal_projection_chart_exists]: supporting
    existence of the adapted orthogonal coordinates for
    2.10.46, p. 203, by adjoint frames and
    their orthogonal extension in 1.7.3–1.7.4.
    The witness proves all chart laws; none is a
    new project axiom or a hypothesis of the final estimate. *)
Theorem orthogonal_projection_chart_exists (R : realType) m k
    (p : {linear R_n R (m+k) -> R_n R k}) :
  O_star p -> exists D : ({linear R_n R (m+k) -> R_n R (m+k)} *
      {linear R_n R (m+k) -> R_n R (m+k)})%type,
    is_orthogonal_projection_chart p D.1 D.2.
Proof.
move=> [a [ha hap]].
have [b [hb hbp]] := @euclidean_right_block_orthogonal_projection R m k.
have [f [hf hfa]] := @orthogonal_injection_transitive R (R_n R k) (R_n R (m+k))
  (@euclidean_inner_product R k) (@euclidean_inner_product R (m+k))
  (@euclidean_inner_productP R k) (@euclidean_inner_productP R (m+k))
  k (@coordinate_basis R k) (m+k) (@coordinate_basis R (m+k))
  (@coordinate_basisP R k) (@coordinate_basisP R (m+k)) a b ha hb.
have [g [hfg [hgf hg]]] := @orthogonal_endomorphism_inverse_exists R (R_n R (m+k))
  (@euclidean_inner_product R (m+k)) (@euclidean_inner_productP R (m+k))
  (m+k) (@coordinate_basis R (m+k)) (@coordinate_basisP R (m+k)) f hf.
exists (f,g); constructor=> // x.
apply: (@inner_vectors_ext R (R_n R k) (@euclidean_inner_product R k)
  (@euclidean_inner_productP R k))=> z.
by rewrite hbp hap -hfa hf.
Qed.

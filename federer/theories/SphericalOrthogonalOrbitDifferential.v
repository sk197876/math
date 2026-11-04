(** Federer (1969), 3.2.47, p. 283: the actual
    differential of Phi(g)=g(c), including its values on the
    printed adapted skew directions. The map is a linear
    ambient evaluation, so its differential is not a premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  OrthonormalFamilies EuclideanHomInnerCharts HomCompositionDeterminant
  EuclideanRankOneInner EuclideanStiefelAdaptedDirections
  NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound
  NormRegularity NormRegularityOperations NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_orthogonal_orbit]: the actual map
    Phi(g)=g(c) in 3.2.47, p. 282, defined on
    the ambient Hom space before restriction to O(n). *)
Definition spherical_orthogonal_orbit (R:realType) N (c:R_n R N):
    Hom (Hom (R_n R N) (R_n R N)) (R_n R N):=
  @HomMap R (Hom (R_n R N) (R_n R N)) (R_n R N)
    (fun g=>g c) (introT (asboolP _) (hom_eval_linear c)).

(** Source for [spherical_orthogonal_orbit_smooth]: actual Phi
    is smooth, supporting the printed diffeomorphism and D Phi
    in 3.2.47, pp. 282–283. Its finite bound is
    proved from the actual Hom basis and norm. *)
Theorem spherical_orthogonal_orbit_smooth (R:realType) N (c:R_n R N):
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_hom_inner_productP R N N))
    (inner_norm_real_norm (@euclidean_inner_productP R N))
    (fun _=>True) (spherical_orthogonal_orbit c).
Proof.
move=>k; apply:norm_class_linear; first by move=>g _; exact:norm_full_domain_interior.
exact (@norm_finite_linear_bounded R (Hom (R_n R N) (R_n R N)) (R_n R N) _ _
  (inner_norm_real_norm (@euclidean_hom_inner_productP R N N))
  (inner_norm_real_norm (@euclidean_inner_productP R N))
  _ (@hom_rank_one_base R (R_n R N) (R_n R N) N N
    (@coordinate_basis R N) (@coordinate_basisP R N) (@coordinate_basis R N))
  (@hom_rank_one_baseP R (R_n R N) (R_n R N) N N
    (@coordinate_basis R N) (@coordinate_basisP R N)
    (@coordinate_basis R N) (@coordinate_basisP R N)) (spherical_orthogonal_orbit c)).
Qed.

(** Source for [spherical_orthogonal_orbit_differential]: the actual
    ambient differential is D Phi(g)w=w(c), supporting its
    tangent restriction in 3.2.47, p. 283. *)
Theorem spherical_orthogonal_orbit_differential (R:realType) N (c:R_n R N) g:
  has_norm_differential (inner_norm (@euclidean_hom_inner_productP R N N))
    (inner_norm (@euclidean_inner_productP R N)) (fun _=>True)
    (spherical_orthogonal_orbit c) g (spherical_orthogonal_orbit c).
Proof.
apply:(@norm_differential_linear R (Hom (R_n R N) (R_n R N)) (R_n R N)
  (inner_norm (@euclidean_hom_inner_productP R N N))
  (inner_norm (@euclidean_inner_productP R N))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R N N))
  (inner_norm_real_norm (@euclidean_inner_productP R N))
  (fun _=>True) g (spherical_orthogonal_orbit c));
  first exact:norm_full_domain_interior.
exact (@norm_finite_linear_bounded R (Hom (R_n R N) (R_n R N)) (R_n R N) _ _
  (inner_norm_real_norm (@euclidean_hom_inner_productP R N N))
  (inner_norm_real_norm (@euclidean_inner_productP R N))
  _ (@hom_rank_one_base R (R_n R N) (R_n R N) N N
    (@coordinate_basis R N) (@coordinate_basisP R N) (@coordinate_basis R N))
  (@hom_rank_one_baseP R (R_n R N) (R_n R N) N N
    (@coordinate_basis R N) (@coordinate_basisP R N)
    (@coordinate_basis R N) (@coordinate_basisP R N)) (spherical_orthogonal_orbit c)).
Qed.

(** Source for [spherical_orthogonal_orbit_skew_image]: actual
    D Phi sends a_ij to 2^(-1/2)(delta_1i v_j-
    delta_1j v_i), 3.2.47, p. 283. The scalar
    is retained explicitly until its normalization is used. *)
Theorem spherical_orthogonal_orbit_skew_image (R:realType) n
    (e:'I_n.+1->R_n R n.+1)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (g:Hom (R_n R n.+1) (R_n R n.+1)) s i j:
  spherical_orthogonal_orbit (e ord0) (euclidean_stiefel_skew_direction g e s i j)=
    s*:((if ord0==i then g (e j) else 0)-
        (if ord0==j then g (e i) else 0)).
Proof.
change (s*:(euclidean_inner_product (e ord0) (e i)*:g (e j)-
  euclidean_inner_product (e ord0) (e j)*:g (e i))=
  s*:((if ord0==i then g (e j) else 0)-
      (if ord0==j then g (e i) else 0))).
rewrite !hON; case:(ord0==i); case:(ord0==j);
  by rewrite ?scale1r ?scale0r.
Qed.

(** Source for [spherical_orthogonal_orbit_first_skew]: the surviving
    a_1j direction has actual image 2^(-1/2)v_j,
    3.2.47, p. 283. *)
Corollary spherical_orthogonal_orbit_first_skew (R:realType) n
    (e:'I_n.+1->R_n R n.+1)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (g:Hom (R_n R n.+1) (R_n R n.+1)) s j:
  j!=ord0 ->spherical_orthogonal_orbit (e ord0)
    (euclidean_stiefel_skew_direction g e s ord0 j)=s*:g (e j).
Proof.
move=>hj; rewrite (spherical_orthogonal_orbit_skew_image hON) eqxx eq_sym (negbTE hj).
by rewrite subr0.
Qed.

(** Source for [spherical_orthogonal_orbit_other_skew]: all
    adapted directions with i>1 and j>1 have actual
    image zero, 3.2.47, p. 283. *)
Corollary spherical_orthogonal_orbit_other_skew (R:realType) n
    (e:'I_n.+1->R_n R n.+1)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (g:Hom (R_n R n.+1) (R_n R n.+1)) s i j:
  i!=ord0 ->j!=ord0 ->spherical_orthogonal_orbit (e ord0)
    (euclidean_stiefel_skew_direction g e s i j)=0.
Proof.
move=>hi hj; rewrite (spherical_orthogonal_orbit_skew_image hON)
  [ord0==i]eq_sym [ord0==j]eq_sym (negbTE hi) (negbTE hj).
by rewrite subrr scaler0.
Qed.

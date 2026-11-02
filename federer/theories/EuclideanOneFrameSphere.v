(** Federer (1969), 3.2.35, p. 271:
    identify the unit sphere with the one-vector
    Stiefel manifold, using the actual Hilbert Hom
    norm and its existing compact manifold theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection InnerProductUP InnerProductLaws InnerNorm InnerMetric HomInner HomInnerCoordinates
  EuclideanHomInnerCharts EuclideanStiefelInnerSplitting EuclideanRankOneInner OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_one_frame_evaluation_norm]:
    supporting the sphere parametrization used for
    boundary rectifiability in Federer 3.2.35,
    p. 271. The one-vector case of the
    Hom inner product in 1.7.9, p. 35,
    has exactly the norm of evaluation at its
    sole unit basis vector. No replacement norm
    or auxiliary scaling factor is introduced. *)
Lemma euclidean_one_frame_evaluation_norm (R:realType) n
    (g:Hom (R_n R 1) (R_n R n)):
  inner_norm (@euclidean_hom_inner_productP R 1 n) g=
    inner_norm (@euclidean_inner_productP R n) (g (@coordinate_basis R 1 ord0)).
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr; symmetry.
rewrite /euclidean_hom_inner_product
  (@hom_inner_orthonormal_sum R (R_n R 1) (R_n R n)
    (@euclidean_inner_product R 1) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R 1) (@euclidean_inner_productP R n)
    1 (@coordinate_basis R 1) (@coordinate_basisP R 1)
    1 (@coordinate_basis R 1) (@coordinate_basisP R 1)
    (@euclidean_coordinate_orthonormal_family R 1)).
by rewrite big_ord1.
Qed.

(** Source for [euclidean_one_frame_sphere_image]:
    the actual sphere identified as O(n,1)
    in Federer 3.2.28(5), p. 267,
    supporting the sphere in the boundary argument
    of 3.2.35, p. 271. Evaluation and
    actual rank-one homomorphisms prove both image
    inclusions, including empty and zero-dimensional
    ambient cases. *)
Theorem euclidean_one_frame_sphere_image (R:realType) n:
  (fun g:inner_metric_space (@euclidean_hom_inner_productP R 1 n)=>
      g (@coordinate_basis R 1 ord0)) @`
    [set g|is_orthogonal_map (@euclidean_inner_product R 1)
      (@euclidean_inner_product R n) (hom_as_linear g)]=
    [set y:R_n R n|inner_norm (@euclidean_inner_productP R n) y= 1].
Proof.
have hBasis:euclidean_inner_product (@coordinate_basis R 1 ord0)
    (@coordinate_basis R 1 ord0)= 1.
  by rewrite euclidean_inner_basis /coordinate_basis ffunE eqxx.
apply/seteqP; split=>y.
- move=>[g hg <-]; apply:inner_norm_value; first exact:ler01.
  have hh:=hg (@coordinate_basis R 1 ord0) (@coordinate_basis R 1 ord0).
  rewrite hBasis in hh.
  by rewrite expr1n; symmetry.
- move=>hy.
  pose g:=euclidean_rank_one_hom (@coordinate_basis R 1 ord0) y.
  have hSquare:euclidean_inner_product y y= 1.
    have hh:=@inner_norm_sqr R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) y.
    rewrite hy expr1n in hh; exact:esym hh.
  exists g; last by change (euclidean_inner_product
    (@coordinate_basis R 1 ord0) (@coordinate_basis R 1 ord0)*:y=y); rewrite hBasis scale1r.
  move=>x z.
  change (euclidean_inner_product
    (euclidean_inner_product x (@coordinate_basis R 1 ord0)*:y)
    (euclidean_inner_product z (@coordinate_basis R 1 ord0)*:y)=euclidean_inner_product x z).
  rewrite !euclidean_inner_basis (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
    (bilZr (inner_bilinear (@euclidean_inner_productP R n))) hSquare.
  change (x ord0*(z ord0*1)=euclidean_inner_product x z).
  by rewrite mulr1 /euclidean_inner_product big_ord1.
Qed.

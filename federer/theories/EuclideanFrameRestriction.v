(** Federer (1969), 3.2.28(3), printed pp. 265–266:
    the forgetful map S(g)=g alpha is linear and smooth,
    with DS(h)=h alpha, and carries actual Stiefel
    tangents into actual Stiefel tangents. In the printed
    application alpha belongs to O(m,m-1), as corrected
    by the erratum, book p. 265 line 12. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm HilbertFormCompactness
  HomCompositionDeterminant OrthogonalMaps AdjointCriteria AdjointLaws EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra EuclideanStiefelTangent
  NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound
  NormRegularity NormRegularityOperations NormOpenDomainLaws TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_frame_restriction]: the actual
    linear map S(g)=g alpha in Federer 3.2.28(3),
    p. 265. Rectangular alpha is retained; the printed
    forgetful case has source dimension m-1 and target m. *)
Definition euclidean_frame_restriction (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)):
    Hom (Hom (R_n R m) (R_n R n)) (Hom (R_n R k) (R_n R n)):=
  @HomMap R (Hom (R_n R m) (R_n R n)) (Hom (R_n R k) (R_n R n))
    (fun g=>hom_comp g alpha) (introT (asboolP _) (hom_precompose_linear alpha)).

(** Source for [euclidean_frame_restriction_smooth]: linearity
    and class infinity of S, Federer 3.2.28(3),
    p. 265, by 3.1.11, p. 221. The source
    and target norms are the actual Hilbert Hom norms. *)
Theorem euclidean_frame_restriction_smooth (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)):
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm_real_norm (@euclidean_hom_inner_productP R k n))
    (fun _=>True) (@euclidean_frame_restriction R k m n alpha).
Proof.
move=>q; apply:norm_class_linear.
- move=>g _; exact:norm_full_domain_interior.
- exact:(norm_finite_linear_bounded
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm_real_norm (@euclidean_hom_inner_productP R k n))
    (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
      (@coordinate_basis R m) (@coordinate_basisP R m)
      (@coordinate_basis R n) (@coordinate_basisP R n)) _).
Qed.

(** Source for [euclidean_frame_restriction_differential]:
    DS(g)h=h alpha, Federer 3.2.28(3), p. 265.
    This is the actual full-domain differential,
    rather than a formal symbolic derivative. *)
Theorem euclidean_frame_restriction_differential (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) g:
  has_norm_differential (inner_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm (@euclidean_hom_inner_productP R k n)) (fun _=>True)
    (@euclidean_frame_restriction R k m n alpha) g
    (@euclidean_frame_restriction R k m n alpha).
Proof.
apply:(@norm_differential_linear R (Hom (R_n R m) (R_n R n))
  (Hom (R_n R k) (R_n R n))
  (inner_norm (@euclidean_hom_inner_productP R m n))
  (inner_norm (@euclidean_hom_inner_productP R k n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R k n))
  (fun _=>True) g (@euclidean_frame_restriction R k m n alpha));
  first exact:norm_full_domain_interior.
exact:(norm_finite_linear_bounded
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R k n))
  (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n)) _).
Qed.

(** Source for [euclidean_frame_restriction_orthogonal]: S
    maps O(n,m) into O(n,m-1), Federer 3.2.28(3),
    p. 265. The composition law also covers arbitrary
    orthogonal rectangular restrictions. *)
Lemma euclidean_frame_restriction_orthogonal (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R m) (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g) ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear (euclidean_frame_restriction n alpha g)).
Proof.
move=>hA hG x y.
change (euclidean_inner_product (g (alpha x)) (g (alpha y))=euclidean_inner_product x y).
rewrite hG; exact:hA.
Qed.

(** Source for [euclidean_frame_restriction_tangent]: DS
    takes the actual tangent of O(n,m) into that of
    O(n,m-1), supporting the adapted-basis calculation
    of Federer 3.2.28(3), pp. 265–266. Both
    tangent identifications are the proved Gram-kernel laws. *)
Theorem euclidean_frame_restriction_tangent (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) (g h:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R m) (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R m n))
    [set f|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear f)] g h ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R k n))
    [set f|is_orthogonal_map (@euclidean_inner_product R k)
      (@euclidean_inner_product R n) (hom_as_linear f)]
    (hom_comp g alpha) (hom_comp h alpha).
Proof.
move=>hA hG hT.
have hGA:is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear (hom_comp g alpha)).
  exact:(@euclidean_frame_restriction_orthogonal R k m n alpha g hA hG).
rewrite (@euclidean_stiefel_tangent R m n g hG) in hT.
rewrite (@euclidean_stiefel_tangent R k n (hom_comp g alpha) hGA).
change (euclidean_gram_differential (hom_comp g alpha) (hom_comp h alpha)=0).
apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R k))=>x.
rewrite hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R k)))
  euclidean_gram_differential_pairing.
change (euclidean_inner_product (h (alpha x)) (g (alpha y))+
  euclidean_inner_product (g (alpha x)) (h (alpha y))=0).
have hZero:euclidean_gram_differential g h=0 by rewrite euclidean_gram_differentialE.
have hPair:=euclidean_gram_differential_pairing g h (alpha x) (alpha y).
rewrite hZero hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R m))) in hPair.
exact:esym hPair.
Qed.

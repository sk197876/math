(** Federer (1969), 3.2.28(3), p. 266:
    the actual forgetful linear map is rectangular
    diagonal in the proved adapted tangent families.
    Every surviving coefficient and every zero direction
    is identified with its actual Hom value. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthogonalMaps EuclideanHyperplaneNormalUP EuclideanRankOneInner EuclideanStiefelAdaptedDirections
  EuclideanStiefelAdaptedBasis EuclideanForgetfulBasisImages EuclideanForgetfulTangentIndices
  EuclideanForgetfulJacobianCoefficients EuclideanSkewIndexCardinality
  EuclideanHomInnerCharts InnerProductUP Bilinear OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section AdaptedImages.
Variable R:realType.
Variables k n r:nat.
Variable alpha:Hom (R_n R k) (R_n R k.+1).
Variable w:R_n R k.+1.
Variable g:Hom (R_n R k.+1) (R_n R n).
Variable e:'I_k.+1->R_n R k.+1.
Variable a:Hom (R_n R r) (R_n R n).
Variable b:Hom (R_n R r.+1) (R_n R n).
Hypothesis hA:is_orthogonal_map (@euclidean_inner_product R k)
  (@euclidean_inner_product R k.+1) (hom_as_linear alpha).
Hypothesis hW:is_euclidean_hyperplane_normal alpha w.
Hypothesis hE:forall i,e (lift ord_max i)=alpha (@coordinate_basis R k i).
Hypothesis hLast:e ord_max=w.
Hypothesis hB:forall j,b (@coordinate_basis R r.+1 (lift ord_max j))=a (@coordinate_basis R r j).
Hypothesis hBLast:b (@coordinate_basis R r.+1 ord_max)=g w.
Local Notation c:=(Num.sqrt (2:R))^-1.
Local Notation FS:=(@euclidean_stiefel_adapted_direction R k.+1 n r g e a).
Local Notation FT:=(@euclidean_stiefel_adapted_direction R k n r.+1 (hom_comp g alpha)
  (@coordinate_basis R k) b).

(** Source for [euclidean_forgetful_adapted_surviving_image]:
    the three nonzero displayed DS basis-image identities
    combined with their injective index matching,
    Federer 3.2.28(3), p. 266. *)
Theorem euclidean_forgetful_adapted_surviving_image j:
  hom_comp (FS (euclidean_forgetful_tangent_index j)) alpha=
    @euclidean_forgetful_tangent_coefficient R k r c j*:FT j.
Proof.
case:j=>[p|[i l]].
- change (hom_comp
    (euclidean_stiefel_skew_direction g e c
      (lift ord_max (val p).1) (lift ord_max (val p).2)) alpha=
    1*:euclidean_stiefel_skew_direction (hom_comp g alpha) (@coordinate_basis R k) c
      (val p).1 (val p).2).
  rewrite scale1r /euclidean_stiefel_skew_direction !hE.
  exact:euclidean_forgetful_skew_image hA.
- case:(unliftP ord_max l)=>[j ->|->].
  + rewrite /euclidean_forgetful_tangent_index liftK
      /euclidean_forgetful_tangent_coefficient lift_eqF scale1r.
    change (hom_comp (euclidean_rank_one_hom (e (lift ord_max i))
      (a (@coordinate_basis R r j))) alpha=
      euclidean_rank_one_hom (@coordinate_basis R k i)
        (b (@coordinate_basis R r.+1 (lift ord_max j)))).
    rewrite hE hB; exact:euclidean_forgetful_normal_image hA.
  + rewrite /euclidean_forgetful_tangent_index unlift_none
      /euclidean_forgetful_tangent_coefficient eqxx.
    change (hom_comp (euclidean_stiefel_skew_direction g e c (lift ord_max i) ord_max) alpha=
      c*:euclidean_rank_one_hom (@coordinate_basis R k i) (b (@coordinate_basis R r.+1 ord_max))).
    rewrite /euclidean_stiefel_skew_direction hE hLast hBLast.
    exact:euclidean_forgetful_cross_image hA hW.
Qed.

(** Source for [euclidean_forgetful_adapted_zero_image]:
    the remaining source b_m,j directions vanish under
    DS, Federer 3.2.28(3), p. 266.
    The original map and adapted normal value are retained. *)
Theorem euclidean_forgetful_adapted_zero_image j:
  hom_comp (FS (inr (ord_max,j))) alpha=0.
Proof.
change (hom_comp (euclidean_rank_one_hom (e ord_max) (a (@coordinate_basis R r j))) alpha=0).
rewrite hLast; exact:euclidean_forgetful_normal_kernel hW.
Qed.
(** Source for [euclidean_forgetful_adapted_pairing]: the
    complete rectangular diagonal matrix of DS in the
    displayed orthonormal tangent families, Federer
    3.2.28(3), p. 266. Exhaustion of source
    directions proves every coefficient, including the
    zero rows, from the actual map values. *)
Theorem euclidean_forgetful_adapted_pairing:
  orthonormal_family (@euclidean_hom_inner_product R k n) FT ->
  forall i j,euclidean_hom_inner_product (hom_comp (FS i) alpha) (FT j)=
    if i==euclidean_forgetful_tangent_index j then
      @euclidean_forgetful_tangent_coefficient R k r c j else 0.
Proof.
move=>hFT i j.
case:(euclidean_forgetful_tangent_index_exhaustion i)=>[[l ->]|[a0 ->]].
- rewrite euclidean_forgetful_adapted_surviving_image
    (bilZl (inner_bilinear (@euclidean_hom_inner_productP R k n))) hFT
    (inj_eq (@euclidean_forgetful_tangent_index_injective k r)).
  change ((@euclidean_forgetful_tangent_coefficient R k r c l)*
    (if l==j then 1 else 0)=if l==j then
      @euclidean_forgetful_tangent_coefficient R k r c j else 0).
  case:(eqVneq l j)=>[->|hNe]; by rewrite ?eqxx ?(negbTE hNe) ?mulr0 ?mulr1.
- rewrite euclidean_forgetful_adapted_zero_image
    (bil0l (inner_bilinear (@euclidean_hom_inner_productP R k n))).
  have hNe:inr (ord_max,a0)!=euclidean_forgetful_tangent_index j.
    rewrite eq_sym; exact:euclidean_forgetful_tangent_index_kernel_disjoint.
  by rewrite (negbTE hNe).
Qed.
End AdaptedImages.

(** Federer (1969), 3.2.28(2), printed p. 264:
    rank DQ on the actual Stiefel tangent kernel is m(n-m).
    The horizontal isometry and the exact zero vertical
    derivative identify its whole image, not only a lower bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP FamilyUpdate ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps
  ExteriorGrading FiniteExteriorPowers ExteriorIndices FiniteOrdinalBasis LinearBasis
  EuclideanRectangularAdjoint EuclideanStiefelSubspaces EuclideanStiefelTangentSplit
  EuclideanGramDifferentialAlgebra EuclideanExteriorWordCoefficient
  EuclideanExteriorVerticalKernel EuclideanExteriorHorizontalRank
  LinearRankUP LinearRankImageInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_tangent_rank]: the exact
    rank m(n-m) of Q in Federer 3.2.28(2), p. 264.
    Its whole tangent image equals its horizontal image;
    both inclusions are proved from the printed decomposition.
    No positive-degree restriction is needed for this rank law. *)
Theorem euclidean_exterior_tangent_rank (R:realType) m n
    (h2:(1+1:R)!=0) (g:Hom (R_n R m) (R_n R n))
    (L:Hom (Hom (R_n R m) (R_n R n)) (exterior_power (R_n R n) m)):
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  has_linear_rank (hom_comp L (hom_of_linear
    (subspace_inclusion (euclidean_stiefel_tangent_subspace g)))) (m*(n-m)).
Proof.
move=>hm hg hL.
pose T:=euclidean_stiefel_tangent_subspace g.
pose Z:=euclidean_stiefel_horizontal_subspace g.
pose LT:=hom_comp L (hom_of_linear (subspace_inclusion T)).
pose LZ:=hom_comp L (hom_of_linear (subspace_inclusion Z)).
have hZ:has_linear_rank LZ (m*(n-m)):=euclidean_exterior_horizontal_rank h2 hm hg hL.
have hY:=@finite_e_lambda_basis R n (R_n R n) (@coordinate_basis R n)
  (@coordinate_basisP R n) h2 m.
have [r [hT hBound]]:=linear_rank_exists LT (finite_ordinal_basis hY).
have hTZ:(r<=m*(n-m))%N.
  apply:(linear_rank_image_inclusion hT hZ)=>h.
  have hh:=subspace_valP h.
  change (euclidean_gram_differential g (subspace_val h)=0) in hh.
  have [hz [hu hSplit]]:=euclidean_stiefel_horizontal_split hg hh.
  pose u:=hom_comp (euclidean_rectangular_adjoint g) (subspace_val h).
  pose z:=subspace_val h-hom_comp g u.
  exists (@subspace_lift R (Hom (R_n R m) (R_n R n)) Z z hz).
  change (L z=L (subspace_val h)).
  have hV:L (hom_comp g u)=0:=euclidean_exterior_vertical_differential_zero hL hu.
  have ht:=congr1 L hSplit.
  change (L (subspace_val h)=L (z+hom_comp g u)) in ht.
  rewrite linearD /= hV addr0 in ht.
  exact:esym ht.
have hZT:(m*(n-m)<=r)%N.
  apply:(linear_rank_image_inclusion hZ hT)=>z.
  have hz:=subspace_valP z.
  change (hom_comp (euclidean_rectangular_adjoint g) (subspace_val z)=0) in hz.
  have ht:=euclidean_stiefel_horizontal_kernel hz.
  exists (@subspace_lift R (Hom (R_n R m) (R_n R n)) T (subspace_val z) ht).
  reflexivity.
have hr:r=(m*(n-m))%N by apply/eqP; rewrite eqn_leq hTZ hZT.
by rewrite -hr.
Qed.

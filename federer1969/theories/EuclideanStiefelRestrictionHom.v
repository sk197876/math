(** Federer (1969), 3.2.28(3), pp. 265–266:
    the actual differential h to h alpha restricts
    to a linear map between the actual tangent
    spaces. Existence exposes only its evaluation law. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm OrthogonalMaps EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra EuclideanHomInnerCharts
  EuclideanStiefelSubspaces EuclideanStiefelTangent EuclideanFrameRestriction TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_restriction_hom_exists]:
    DS on the actual tangent spaces in Federer
    3.2.28(3), p. 266. The specification
    is its precise restriction value; both linearity
    and tangent membership are proved. *)
Theorem euclidean_stiefel_restriction_hom_exists (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R m)
    (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  exists S:Hom (subspace_space (euclidean_stiefel_tangent_subspace g))
    (subspace_space (euclidean_stiefel_tangent_subspace (hom_comp g alpha))),
    forall h,subspace_val (S h)=hom_comp (subspace_val h) alpha.
Proof.
move=>hA hG.
pose X:=Hom (R_n R m) (R_n R n).
pose Y:=Hom (R_n R k) (R_n R n).
pose T:=euclidean_stiefel_tangent_subspace g.
pose U:=euclidean_stiefel_tangent_subspace (hom_comp g alpha).
have hGA:is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear (hom_comp g alpha)).
  move=>x y; change (euclidean_inner_product (g (alpha x)) (g (alpha y))=euclidean_inner_product x y).
  rewrite hG; exact:hA.
have hMember (h:subspace_space T):U (hom_comp (subspace_val h) alpha).
  have hKernel:=subspace_valP h.
  change (euclidean_gram_differential g (subspace_val h)=0) in hKernel.
  have hTan:norm_tangent_cone (inner_norm (@EuclideanHomInnerCharts.euclidean_hom_inner_productP R m n))
      [set f|is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear f)] g (subspace_val h).
    rewrite (@euclidean_stiefel_tangent R m n g hG).
    change (hom_comp (euclidean_rectangular_adjoint (subspace_val h)) g+
      hom_comp (euclidean_rectangular_adjoint g) (subspace_val h)=0).
    by rewrite -euclidean_gram_differentialE.
  have hTarget:=@euclidean_frame_restriction_tangent R k m n alpha g (subspace_val h) hA hG hTan.
  rewrite (@euclidean_stiefel_tangent R k n (hom_comp g alpha) hGA) in hTarget.
  change (euclidean_gram_differential (hom_comp g alpha) (hom_comp (subspace_val h) alpha)=0).
  rewrite euclidean_gram_differentialE; exact hTarget.
pose F (h:subspace_space T):subspace_space U:=subspace_lift (hMember h).
have hF:linear F.
  move=>c h t; apply:subspace_val_injective.
  rewrite /F !subspace_liftE.
  rewrite !linearD !linearZ ?subspace_liftE.
  apply:hom_ext=>x.
  change (c*:(subspace_val h (alpha x))+subspace_val t (alpha x)=
    c*:(subspace_val h (alpha x))+subspace_val t (alpha x)).
  reflexivity.
exists (@HomMap R (subspace_space T) (subspace_space U) F (introT (asboolP _) hF)).
by move=>h.
Qed.

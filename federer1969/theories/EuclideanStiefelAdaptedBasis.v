(** Federer (1969), 3.2.28(3), p. 265:
    the displayed skew and normal directions form a
    full orthonormal basis of the actual Stiefel tangent.
    Membership, orthonormality and the exact dimension
    are proved before the basis conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces SubspaceEquality
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerProductRestriction OrthogonalMaps OrthonormalFamilies LinearBasis FiniteDimension FiniteBasisCriterion HomCompositionDeterminant
  EuclideanHomInnerCharts EuclideanGramDifferentialAlgebra EuclideanRectangularAdjoint EuclideanStiefelInnerSplitting
  EuclideanStiefelSubspaces EuclideanStiefelTangent EuclideanStiefelSmooth FiniteInnerSmoothSubmanifoldUP
  FiniteInnerTangentPlane TangentConeUP EuclideanFrameComplementUP EuclideanRankOneInner
  EuclideanStiefelAdaptedDirections EuclideanStiefelAdaptedOrthonormal EuclideanStiefelHalfNormalization
  EuclideanStiefelTangentIndexDimension EuclideanSkewIndexCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_tangent_dimension]:
    the actual tangent has dimension m(2n-m-1)/2,
    Federer 3.2.28(1),(3), pp. 263,265, by
    the proved manifold and tangent assertions. *)
Theorem euclidean_stiefel_tangent_dimension (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  exists b:'I_(m*(2*n-m-1)%/2)->subspace_space (euclidean_stiefel_tangent_subspace g),
    is_basis b.
Proof.
move=>hG.
pose X:=Hom (R_n R m) (R_n R n).
pose S:set X:=[set f|is_orthogonal_map (@euclidean_inner_product R m)
  (@euclidean_inner_product R n) (hom_as_linear f)].
pose T:=euclidean_stiefel_tangent_subspace g.
have hMan:=inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R m n) 1%N.
have [W hW]:=@finite_inner_submanifold_tangent_plane R X _
  (@euclidean_hom_inner_productP R m n) _ _
  (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n (@coordinate_basis R m)
    (@coordinate_basisP R m) (@coordinate_basis R n) (@coordinate_basisP R n))
  (m*(2*n-m-1)%/2) 1 S g (leqnn 1) hMan hG.
rewrite (@euclidean_stiefel_tangent R m n g hG) in hW.
have hEqual:T=grassmann_val W.
  apply:subspace_ext=>h.
  have hPoint:=congr1 (fun A:set X=>A h) hW.
  change ((hom_comp (euclidean_rectangular_adjoint h) g+
    hom_comp (euclidean_rectangular_adjoint g) h=0)=grassmann_val W h) in hPoint.
  change (T h <->grassmann_val W h).
  change (euclidean_gram_differential g h=0 <->grassmann_val W h).
  rewrite euclidean_gram_differentialE; by rewrite hPoint.
have hb:=grassmann_proof W; by rewrite -hEqual in hb.
Qed.

Section AdaptedBasis.
Variable R:realType.
Variables m n r:nat.
Variable g:Hom (R_n R m) (R_n R n).
Variable e:'I_m->R_n R m.
Variable a:Hom (R_n R r) (R_n R n).
Hypothesis hG:is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g).
Hypothesis hE:orthonormal_family (@euclidean_inner_product R m) e.
Hypothesis hA:is_orthogonal_map (@euclidean_inner_product R r)
  (@euclidean_inner_product R n) (hom_as_linear a).
Hypothesis hNormal:forall u,euclidean_rectangular_adjoint g (a u)=0.
Local Notation I:=((euclidean_skew_indices m)+('I_m*'I_r))%type.
Local Notation T:=(euclidean_stiefel_tangent_subspace g).
Local Notation c:=(Num.sqrt (2:R))^-1.

(** Source for [euclidean_stiefel_adapted_direction]: the
    single indexed family consisting of the a_ij and
    b_ij displayed in Federer 3.2.28(3), p. 265.
    The target normal frame is specified by its
    orthonormality and perpendicularity laws and is not chosen globally. *)
Definition euclidean_stiefel_adapted_direction (i:I):Hom (R_n R m) (R_n R n):=
  match i with
  | inl q=>euclidean_stiefel_skew_direction g e c (val q).1 (val q).2
  | inr q=>euclidean_rank_one_hom (e q.1) (a (@coordinate_basis R r q.2))
  end.

(** Source for [euclidean_stiefel_adapted_direction_member]:
    all displayed directions satisfy the actual tangent
    equations, Federer 3.2.28(3), p. 265. *)
Lemma euclidean_stiefel_adapted_direction_member i:T (euclidean_stiefel_adapted_direction i).
Proof.
case:i=>q.
- change (euclidean_gram_differential g (euclidean_stiefel_skew_direction g e c (val q).1 (val q).2)=0).
  exact:euclidean_stiefel_skew_direction_tangent hG.
- change (euclidean_gram_differential g
    (euclidean_rank_one_hom (e q.1) (a (@coordinate_basis R r q.2)))=0).
  exact:euclidean_stiefel_normal_direction_tangent (hNormal _).
Qed.

(** Source for [euclidean_stiefel_adapted_directions_orthonormal]:
    the entire displayed family is orthonormal in the
    actual Hilbert Hom product, Federer 3.2.28(3),
    p. 265. Mixed pairings vanish by the exact
    normal-complement law. *)
Theorem euclidean_stiefel_adapted_directions_orthonormal:
  orthonormal_family (@euclidean_hom_inner_product R m n) euclidean_stiefel_adapted_direction.
Proof.
have hN:orthonormal_family (@euclidean_inner_product R n)
    (fun j=>a (@coordinate_basis R r j)).
  move=>i j; rewrite hA.
  exact:(@EuclideanStiefelInnerSplitting.euclidean_coordinate_orthonormal_family R r i j).
move=>[i|i] [j|j] /=.
- exact:(@euclidean_stiefel_normalized_skew_family R m n g e hG hE i j).
- exact:euclidean_stiefel_skew_normal_orthogonal (hNormal _).
- rewrite (inner_symmetric (@euclidean_hom_inner_productP R m n)).
  exact:euclidean_stiefel_skew_normal_orthogonal (hNormal _).
- exact:(@euclidean_stiefel_normal_family_orthonormal R m n r e
    (fun j=>a (@coordinate_basis R r j)) hE hN i j).
Qed.

(** Source for [euclidean_stiefel_adapted_tangent_basis]: the
    displayed orthonormal family is a full tangent basis,
    Federer 3.2.28(3), p. 265. Independence follows
    from orthonormality; its cardinality equals the actual
    tangent dimension proved in part (1). *)
Theorem euclidean_stiefel_adapted_tangent_basis:
  (m<=n)%N ->r=(n-m)%N ->
  is_basis (fun i:I=>@subspace_lift R (Hom (R_n R m) (R_n R n)) T
    (euclidean_stiefel_adapted_direction i) (euclidean_stiefel_adapted_direction_member i)).
Proof.
move=>hmn hr.
have [b hb]:=euclidean_stiefel_tangent_dimension hG.
pose f:=fun i:I=>@subspace_lift R (Hom (R_n R m) (R_n R n)) T
  (euclidean_stiefel_adapted_direction i) (euclidean_stiefel_adapted_direction_member i).
have hO:orthonormal_family (@restricted_inner_product R (Hom (R_n R m) (R_n R n))
    (@euclidean_hom_inner_product R m n) T) f:=euclidean_stiefel_adapted_directions_orthonormal.
apply:(@finite_independent_basis_card R (finite_basis_vect hb) I f).
- rewrite finite_basis_dimension card_ord.
  have hCard:=euclidean_stiefel_tangent_index_cardinality hmn.
  rewrite /euclidean_stiefel_tangent_indices -hr in hCard; exact:esym hCard.
- exact:(orthonormal_independent
    (restricted_inner_productP (@euclidean_hom_inner_productP R m n) T) hO).
Qed.
End AdaptedBasis.

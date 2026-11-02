(** Federer (1969), 3.2.28(3), p. 265:
    choose the orthonormal source basis adapted to
    im alpha, with its prescribed unit normal last.
    This is a proved local existence assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws OrthogonalMaps OrthonormalFamilies
  InnerNormalization InfiniteSequence EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP
  EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hyperplane_adapted_frame_exists]:
    the adapted e_1,...,e_m in Federer 3.2.28(3),
    p. 265. The first m-1 vectors are
    exactly alpha of the standard source basis;
    the last is the abstract unit normal. *)
Theorem euclidean_hyperplane_adapted_frame_exists (R:realType) k
    (alpha:Hom (R_n R k) (R_n R k.+1)) w:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  exists e:'I_k.+1->R_n R k.+1,
    orthonormal_family (@euclidean_inner_product R k.+1) e /\
    (forall i,e (lift ord_max i)=alpha (@coordinate_basis R k i)) /\e ord_max=w.
Proof.
move=>hA hW.
pose u:=fun i=>alpha (@coordinate_basis R k i).
exists (ordinal_snoc u w); split.
- apply:(@orthonormal_snoc R (R_n R k.+1) (@euclidean_inner_product R k.+1)
    (@euclidean_inner_productP R k.+1) k u w).
  + move=>i j; rewrite /u hA; exact:euclidean_coordinate_orthonormal_family.
  + exact:hyperplane_normal_unit hW.
  + move=>i; rewrite (inner_symmetric (@euclidean_inner_productP R k.+1)) /u
      -euclidean_rectangular_adjoint_pairing (hyperplane_normal_perpendicular hW).
    by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k))).
- split; first by move=>i; rewrite ordinal_snoc_lift.
  exact:ordinal_snoc_last.
Qed.

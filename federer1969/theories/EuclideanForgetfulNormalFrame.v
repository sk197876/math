(** Federer (1969), 3.2.28(3), pp. 265–266:
    normal directions for the restricted target frame
    consist of the last retained frame vector g(w)
    and the old normal directions. Existence is proved
    with the prescribed values and orthogonality laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerProductLaws AdjointLaws OrthogonalMaps OrthonormalFamilies InnerNormalization InfiniteSequence
  BasisInterpolation LinearBasis OrthogonalBasisCriteria EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP
  EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_forgetful_normal_frame_exists]:
    the target adapted v_j in the c_ij,d_ij basis,
    Federer 3.2.28(3), pp. 265–266. Append
    g(w) to the old normal frame and prove
    the restricted-frame normal law on every vector. *)
Theorem euclidean_forgetful_normal_frame_exists (R:realType) k n r
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (g:Hom (R_n R k.+1) (R_n R n)) (a:Hom (R_n R r) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  is_orthogonal_map (@euclidean_inner_product R r) (@euclidean_inner_product R n)
    (hom_as_linear a) ->
  (forall z,euclidean_rectangular_adjoint g (a z)=0) ->
  exists b:Hom (R_n R r.+1) (R_n R n),
    is_orthogonal_map (@euclidean_inner_product R r.+1) (@euclidean_inner_product R n)
      (hom_as_linear b) /\
    (forall z,euclidean_rectangular_adjoint (hom_comp g alpha) (b z)=0) /\
    (forall i,b (@coordinate_basis R r.+1 (lift ord_max i))=a (@coordinate_basis R r i)) /\
    b (@coordinate_basis R r.+1 ord_max)=g w.
Proof.
move=>hA hW hG hOrtho hNormal.
pose u:=fun i=>a (@coordinate_basis R r i).
pose v:=ordinal_snoc u (g w).
have hU:orthonormal_family (@euclidean_inner_product R n) u.
  move=>i j; rewrite /u hOrtho; exact:euclidean_coordinate_orthonormal_family.
have hCross z x:euclidean_inner_product (g x) (a z)=0.
  rewrite -euclidean_rectangular_adjoint_pairing hNormal.
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k.+1))).
have hV:orthonormal_family (@euclidean_inner_product R n) v.
  apply:(@orthonormal_snoc R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) r u (g w) hU).
  - rewrite hG; exact:hyperplane_normal_unit hW.
  - move=>i; exact:hCross.
pose f:=basis_interpolation (@coordinate_basisP R r.+1) v.
pose b:=hom_of_linear f.
have hEval i:b (@coordinate_basis R r.+1 i)=v i.
  exact:basis_interpolationE.
have hB:is_orthogonal_map (@euclidean_inner_product R r.+1) (@euclidean_inner_product R n)
    (hom_as_linear b).
  apply:(@orthogonal_map_basis_criterion R (R_n R r.+1) (R_n R n)
    (@euclidean_inner_product R r.+1) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R r.+1) (@euclidean_inner_productP R n)
    r.+1 (@coordinate_basis R r.+1) (@coordinate_basisP R r.+1)
    (@euclidean_coordinate_orthonormal_family R r.+1) (hom_as_linear b)).
  move=>i j.
  change (euclidean_inner_product (b (@coordinate_basis R r.+1 i))
    (b (@coordinate_basis R r.+1 j))=if i==j then 1 else 0).
  by rewrite !hEval; exact:hV.
have hPerp i:euclidean_rectangular_adjoint (hom_comp g alpha) (v i)=0.
  apply:(inner_vectors_ext (@euclidean_inner_productP R k))=>x.
  rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k)))
    euclidean_rectangular_adjoint_pairing hom_compE.
  case:(unliftP ord_max i)=>[j ->|->].
  - rewrite /v ordinal_snoc_lift /u; exact:hCross.
  - rewrite /v ordinal_snoc_last hG -euclidean_rectangular_adjoint_pairing
      (hyperplane_normal_perpendicular hW).
    by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k))).
have hAll:forall z,euclidean_rectangular_adjoint (hom_comp g alpha) (b z)=0.
  apply:(basis_linear_ext (@coordinate_basisP R r.+1)
    (linear_comp (hom_as_linear (euclidean_rectangular_adjoint (hom_comp g alpha))) (hom_as_linear b))
    (hom_as_linear (0:Hom (R_n R r.+1) (R_n R k)))).
  move=>i.
  change (euclidean_rectangular_adjoint (hom_comp g alpha) (b (@coordinate_basis R r.+1 i))=0).
  by rewrite hEval; exact:hPerp.
exists b; split; first exact hB.
split; first exact hAll.
split.
- by move=>i; rewrite hEval /v ordinal_snoc_lift.
- by rewrite hEval /v ordinal_snoc_last.
Qed.

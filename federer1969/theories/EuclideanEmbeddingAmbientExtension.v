(** Federer (1969), 3.2.36, p. 273: extend an actual
    orthogonal injection to a common ambient orthogonal transformation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP LinearBasis CoordinateProjection OrthogonalMaps OrthonormalFamilies
  OrthonormalCapacityExtension OrthonormalFrameMap EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockLinearMaps EuclideanCartesianLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_embedding_ambient_extension]: the ambient
    orthogonal extension needed for the isometric-injection conclusion
    of Federer 3.2.36, p. 273. Embed both coordinate spaces in
    R^(m+n), extend the prescribed orthonormal m-frame using 1.7.1--3,
    pp. 28--30, and use finite-basis extensionality for the exact
    restriction. All choices are local existence witnesses; no dimension
    inequality, chosen global completion or private implementation is used. *)
Theorem euclidean_embedding_ambient_extension (R:realType) m n
    (g:{linear R_n R m->R_n R n}):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) g ->
  exists T:{linear R_n R (m+n)->R_n R (m+n)},
    is_orthogonal_map (@euclidean_inner_product R (m+n)) (@euclidean_inner_product R (m+n)) T /\
    forall x,T (@euclidean_first_injection R m n x)=
      @euclidean_last_injection R m n (g x).
Proof.
move=>hG.
pose V:=R_n R (m+n).
pose e (i:'I_m):V:=@euclidean_block_join R m n (0,g (@coordinate_basis R m i)).
have hE:orthonormal_family (@euclidean_inner_product R (m+n)) e.
  move=>i j; rewrite /e euclidean_block_join_inner.
  rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R m))) add0r hG.
  by rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hCoordinate:orthonormal_family (@euclidean_inner_product R (m+n)) (@coordinate_basis R (m+n)).
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hIndependent:=@orthonormal_independent R V (@euclidean_inner_product R (m+n))
  (@euclidean_inner_productP R (m+n)) [the finType of 'I_(m+n)] (@coordinate_basis R (m+n)) hCoordinate.
have hSize:(m<=m+n)%N:=leq_addr n m.
have [frame [hFrame hFrameE]]:=@orthonormal_capacity_extension R V (@euclidean_inner_product R (m+n))
  (@euclidean_inner_productP R (m+n)) (m+n) (@coordinate_basis R (m+n)) hIndependent m e hE hSize.
have [T [hT hTBasis]]:=@orthonormal_frame_map_exists R V (@euclidean_inner_product R (m+n))
  (@euclidean_inner_productP R (m+n)) (m+n) frame hFrame.
exists T; split=>//.
pose F:=linear_comp T (hom_as_linear (@euclidean_first_injection_map R m n)).
pose H:=linear_comp (hom_as_linear (@euclidean_last_injection_map R m n)) g.
have hBasis i:F (@coordinate_basis R m i)=H (@coordinate_basis R m i).
  change (T (@euclidean_first_injection R m n (@coordinate_basis R m i))=
    @euclidean_last_injection R m n (g (@coordinate_basis R m i))).
  rewrite euclidean_first_injection_basis.
  have hIndex:lshift n i=widen_ord hSize i by apply:val_inj.
  by rewrite hIndex hTBasis hFrameE.
move=>x; exact:(basis_linear_ext (@coordinate_basisP R m) F H hBasis x).
Qed.

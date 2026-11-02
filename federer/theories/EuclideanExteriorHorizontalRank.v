(** Federer (1969), 3.2.28(2), printed p. 264:
    the horizontal differential of Q has rank m(n-m).
    The actual horizontal space, proved dimension and exact
    isometry supply the rank, including the zero-rank cases. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP FamilyUpdate ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps
  ExteriorGrading FiniteExteriorPowers ExteriorIndices FiniteOrdinalBasis LinearBasis
  EuclideanRectangularAdjoint EuclideanStiefelSubspaces EuclideanHorizontalDimension
  EuclideanExteriorWordCoefficient EuclideanExteriorVerticalKernel
  LinearRankUP LinearInjectiveRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_horizontal_restriction_injective]:
    the horizontal restriction of DQ is injective, supporting
    its rank in Federer 3.2.28(2), p. 264. The derivative
    is the proved replacement map, not an assumed isometry. *)
Lemma euclidean_exterior_horizontal_restriction_injective (R:realType) m n
    (h2:(1+1:R)!=0) (g:Hom (R_n R m) (R_n R n))
    (L:Hom (Hom (R_n R m) (R_n R n)) (exterior_power (R_n R n) m)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  injective (hom_comp L (hom_of_linear
    (subspace_inclusion (euclidean_stiefel_horizontal_subspace g)))).
Proof.
move=>hg hL x y heq.
apply:subspace_val_injective.
apply/eqP; rewrite -subr_eq0; apply/eqP.
have hZ:=subspace_valP (x-y).
change (hom_comp (euclidean_rectangular_adjoint g) (subspace_val (x-y))=0) in hZ.
have hLz:L (subspace_val (x-y))=0.
  rewrite !linearB.
  change (L (subspace_val x)-L (subspace_val y)=0).
  change (L (subspace_val x)=L (subspace_val y)) in heq.
  by rewrite heq subrr.
have hz:=euclidean_exterior_horizontal_kernel_trivial h2 hg hL hZ hLz.
by rewrite linearB in hz.
Qed.

(** Source for [euclidean_exterior_horizontal_rank]: the
    rank on Z(g) is m(n-m), Federer 3.2.28(2), p. 264.
    This follows from the proved actual dimension and
    injectivity, not a rank assumption or matrix representation. *)
Theorem euclidean_exterior_horizontal_rank (R:realType) m n
    (h2:(1+1:R)!=0) (g:Hom (R_n R m) (R_n R n))
    (L:Hom (Hom (R_n R m) (R_n R n)) (exterior_power (R_n R n) m)):
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  has_linear_rank (hom_comp L (hom_of_linear
    (subspace_inclusion (euclidean_stiefel_horizontal_subspace g)))) (m*(n-m)).
Proof.
move=>hm hg hL.
have [e he]:=euclidean_stiefel_horizontal_dimension hm hg.
have hY:=@finite_e_lambda_basis R n (R_n R n) (@coordinate_basis R n)
  (@coordinate_basisP R n) h2 m.
apply:(@linear_injective_rank R
  (subspace_space (euclidean_stiefel_horizontal_subspace g))
  (exterior_power (R_n R n) m) (m*(n-m)) e he
  #|{:Lambda n m}| (fun i=>@finite_e_lambda R n (R_n R n)
    (@coordinate_basis R n) m (enum_val i)) (finite_ordinal_basis hY)).
exact:(@euclidean_exterior_horizontal_restriction_injective R m n h2 g L hg hL).
Qed.

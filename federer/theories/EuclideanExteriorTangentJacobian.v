(** Federer (1969), 3.2.28(2), printed p. 264:
    the actual tangent exterior Jacobian of Q is one.
    Factor its actual differential through the orthogonal
    horizontal projection and its isometric restriction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP FamilyUpdate Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductRestriction
  OrthogonalMaps AdjointUP LinearBasis InnerNorm InnerExterior InnerExteriorPositivity
  ExteriorGrading ExteriorMaps ExteriorMapScaling OperatorNormUP
  EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra
  EuclideanHomInnerCharts EuclideanStiefelSubspaces EuclideanHorizontalDimension
  EuclideanStiefelHorizontalProjection EuclideanExteriorWordCoefficient
  EuclideanExteriorHorizontalPairing EuclideanExteriorVerticalKernel
  OrthogonalQuotientExteriorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TangentJacobian.
Variable R:realType.
Variables m n:nat.
Variable h2:(1+1:R)!=0.
Variable g:Hom (R_n R m) (R_n R n).
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(exterior_power (R_n R n) m).
Local Notation T:=(euclidean_stiefel_tangent_subspace g).
Local Notation Z:=(euclidean_stiefel_horizontal_subspace g).
Local Notation BT:=(@restricted_inner_product R X (@euclidean_hom_inner_product R m n) T).
Local Notation BZ:=(@restricted_inner_product R X (@euclidean_hom_inner_product R m n) Z).
Local Notation hBT:=(@restricted_inner_productP R X (@euclidean_hom_inner_product R m n)
  (@euclidean_hom_inner_productP R m n) T).
Local Notation hBZ:=(@restricted_inner_productP R X (@euclidean_hom_inner_product R m n)
  (@euclidean_hom_inner_productP R m n) Z).
Local Notation BY:=(@exterior_inner_form R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
Local Notation hBY:=(@exterior_inner_productP R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).

(** Source for [euclidean_exterior_tangent_jacobian_one]:
    J_{m(n-m)}Q(g)=1, Federer 3.2.28(2), p. 264.
    This proves the actual exterior operator-norm laws,
    including attainment, in the exact tangent Hilbert metric.
    The supporting norm identity includes degree zero. *)
Theorem euclidean_exterior_tangent_jacobian_one (L:Hom X Y):
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  is_operator_norm (exterior_inner_productP h2 hBT (m*(n-m)))
    (exterior_inner_productP h2 hBY (m*(n-m)))
    (exterior_power_map (hom_as_linear (hom_comp L
      (hom_of_linear (subspace_inclusion T)))) (m*(n-m))) 1.
Proof.
move=>hm hg hL.
have [H [P [hH [hP [hHe hPe]]]]]:=euclidean_stiefel_horizontal_projection_exists hm hg.
pose A:=hom_comp L (hom_of_linear (subspace_inclusion Z)).
pose LT:=hom_comp L (hom_of_linear (subspace_inclusion T)).
have hA:is_orthogonal_map BZ BY (hom_as_linear A).
  move=>z w.
  exact:(@euclidean_exterior_horizontal_differential_pairing R m n h2 g L hg hL
    (subspace_val z) (subspace_val w) (subspace_valP z) (subspace_valP w)).
have hEq:hom_as_linear LT=1 linear_comp (hom_as_linear A) (hom_as_linear P).
  move=>h.
  change (L (subspace_val h)=L (subspace_val (P h))).
  rewrite hPe linearB.
  change (L (subspace_val h)=L (subspace_val h)-L
    (hom_comp g (hom_comp (euclidean_rectangular_adjoint g) (subspace_val h)))).
  have hh:=subspace_valP h.
  change (euclidean_gram_differential g (subspace_val h)=0) in hh.
  have hu:=(euclidean_gram_kernel_skew g (subspace_val h)).1 hh.
  by rewrite (euclidean_exterior_vertical_differential_zero hL hu) subr0.
have [b hb]:=euclidean_stiefel_horizontal_dimension hm hg.
have hOne:=@orthogonal_quotient_top_exterior_norm_one R h2
  (subspace_space Z) (subspace_space T) Y BZ BT BY hBZ hBT hBY
  (m*(n-m)) b hb (hom_as_linear H) (hom_as_linear P) (hom_as_linear A) hH hP hA.
have hMap:=@exterior_power_map_ext R (subspace_space T) Y (hom_as_linear LT)
  (linear_comp (hom_as_linear A) (hom_as_linear P)) hEq (m*(n-m))%N.
constructor.
- move=>x hx.
  have hBound:=@operator_norm_unit_bound R _ _ _ _ _ _ _ 1 hOne x hx.
  by rewrite -hMap in hBound.
- have [x [hx hValue]]:=operator_norm_attained hOne.
  exists x; split; first exact hx.
  by rewrite hMap.
Qed.
End TangentJacobian.

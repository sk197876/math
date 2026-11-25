(** Federer (1969), 3.2.28(2), printed p. 264:
    the orthogonal projection of the Stiefel tangent onto
    Z(g) is h to h-g g* h. Existence uses the
    sealed adjoint of the actual horizontal inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerProductRestriction OrthogonalMaps AdjointUP AdjointLaws Adjoint
  EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra
  EuclideanHomInnerCharts EuclideanStiefelSubspaces EuclideanStiefelTangentSplit
  EuclideanStiefelInnerSplitting EuclideanHorizontalDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section HorizontalProjection.
Variable R:realType.
Variables m n:nat.
Variable g:Hom (R_n R m) (R_n R n).
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation T:=(euclidean_stiefel_tangent_subspace g).
Local Notation Z:=(euclidean_stiefel_horizontal_subspace g).
Local Notation BT:=(@restricted_inner_product R X (@euclidean_hom_inner_product R m n) T).
Local Notation BZ:=(@restricted_inner_product R X (@euclidean_hom_inner_product R m n) Z).
Local Notation hBT:=(@restricted_inner_productP R X (@euclidean_hom_inner_product R m n)
  (@euclidean_hom_inner_productP R m n) T).
Local Notation hBZ:=(@restricted_inner_productP R X (@euclidean_hom_inner_product R m n)
  (@euclidean_hom_inner_productP R m n) Z).

(** Source for [euclidean_stiefel_horizontal_projection_exists]:
    the exact orthogonal projection onto Z(g), supporting
    ker DQ=Z(g) perpendicular and JQ=1 in Federer
    3.2.28(2), p. 264. Its formulas and adjoint
    laws are proved; no global projection is selected. *)
Theorem euclidean_stiefel_horizontal_projection_exists:
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  exists (H:Hom (subspace_space Z) (subspace_space T))
    (P:Hom (subspace_space T) (subspace_space Z)),
    is_orthogonal_map BZ BT (hom_as_linear H) /\
    is_adjoint BZ BT (hom_as_linear H) (hom_as_linear P) /\
    (forall z,subspace_val (H z)=subspace_val z) /\
    forall h,subspace_val (P h)=subspace_val h-
      hom_comp g (hom_comp (euclidean_rectangular_adjoint g) (subspace_val h)).
Proof.
move=>hm hg.
have hIncl (z:subspace_space Z):T (subspace_val z).
  exact:euclidean_stiefel_horizontal_kernel (subspace_valP z).
pose F (z:subspace_space Z):subspace_space T:=subspace_lift (hIncl z).
have hF:linear F.
  move=>c z w; apply:subspace_val_injective.
  by rewrite linearD linearZ /F !subspace_liftE linearD linearZ.
pose H:=@HomMap R (subspace_space Z) (subspace_space T) F
  (introT (asboolP _) hF).
have hHe z:subspace_val (H z)=subspace_val z by [].
have hHo:is_orthogonal_map BZ BT (hom_as_linear H).
  by move=>z w; rewrite /restricted_inner_product !hHe.
have [b hb]:=euclidean_stiefel_horizontal_dimension hm hg.
pose P:=hom_of_linear (@inner_adjoint R (subspace_space Z) (subspace_space T)
  BZ BT hBZ hBT (m*(n-m)) b hb (hom_as_linear H)).
have hP:is_adjoint BZ BT (hom_as_linear H) (hom_as_linear P):=inner_adjointP hBZ hBT hb (hom_as_linear H).
exists H,P; split; first exact hHo.
split; first exact hP.
split; first exact hHe.
move=>h.
have hh:=subspace_valP h.
change (euclidean_gram_differential g (subspace_val h)=0) in hh.
have [hZ [hU hSplit]]:=euclidean_stiefel_horizontal_split hg hh.
pose z:subspace_space Z:=@subspace_lift R X Z _ hZ.
have hEq:P h=z.
  apply:(inner_vectors_ext hBZ)=>w.
  rewrite hP /restricted_inner_product hHe /z subspace_liftE.
  rewrite (bilBr (inner_bilinear (@euclidean_hom_inner_productP R m n))).
  have hZero:=euclidean_stiefel_horizontal_vertical_orthogonal
    (hom_comp (euclidean_rectangular_adjoint g) (subspace_val h)) (subspace_valP w).
  by rewrite hZero subr0.
by rewrite hEq /z subspace_liftE.
Qed.
End HorizontalProjection.

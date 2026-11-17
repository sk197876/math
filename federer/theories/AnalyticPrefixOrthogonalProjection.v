(** Federer (1969), 3.4.8(1), p. 326:
    the original dual orthonormal bases make p_j an
    orthogonal projection. Basis-pair equations prove the
    auxiliary inclusion is isometric and its adjoint is p_j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom LinearBasis GrassmannAbbreviations FiniteCoordinates
  InnerProductUP EuclideanInnerProduct OrthonormalFamilies OrthogonalMaps AdjointUP
  BilinearPrecompose BilinearBasisExt CoordinateProjection AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrthogonalPrefix.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hOrtho:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable j:nat.
Hypothesis hjn:(j<=n)%N.
Variable P:Hom X (R_n R j).
Variable S:Hom (R_n R j) X.
Hypothesis hP:is_analytic_prefix_projection omega hjn P.
Hypothesis hS:is_analytic_prefix_section e hjn S.
Local Notation Y:=(R_n R j).
Local Notation C:=(@euclidean_inner_product R j).
Local Notation hC:=(@euclidean_inner_productP R j).

(** Source for [analytic_prefix_inclusion_orthogonal]: the
    original prefix inclusion preserves the original inner
    product, supporting p_j in O*(n,j), 3.4.8(1), p. 326. *)
Lemma analytic_prefix_inclusion_orthogonal:
  is_orthogonal_map C B (hom_as_linear S).
Proof.
apply:(@bilinear_basis_ext R (Choice.clone 'I_j _) (Choice.clone 'I_j _)
  Y Y R^o (@coordinate_basis R j) (@coordinate_basis R j)
  (@coordinate_basisP R j) (@coordinate_basisP R j)
  (fun x y=>B (hom_as_linear S x) (hom_as_linear S y)) C
  (@bilinear_linear_precompose R Y Y X X R^o B (inner_bilinear hB)
    (hom_as_linear S) (hom_as_linear S)) (inner_bilinear hC))=>i k.
rewrite !hom_as_linearE !hS hOrtho euclidean_inner_basis /coordinate_basis ffunE.
by rewrite -!val_eqE /= eq_sym.
Qed.

(** Source for [analytic_prefix_projection_adjoint]: the original
    p_j is the adjoint of its prefix inclusion,
    supporting 3.4.8(1), p. 326. *)
Lemma analytic_prefix_projection_adjoint:
  is_adjoint C B (hom_as_linear S) (hom_as_linear P).
Proof.
apply:(@bilinear_basis_ext R (Choice.clone 'I_j _) (Choice.clone 'I_n _)
  Y X R^o (@coordinate_basis R j) e (@coordinate_basisP R j) he
  (fun z x=>C z (hom_as_linear P x)) (fun z x=>B (hom_as_linear S z) x)
  (@bilinear_linear_precompose R Y X Y Y R^o C (inner_bilinear hC)
    (linear_id Y) (hom_as_linear P))
  (@bilinear_linear_precompose R Y X X X R^o B (inner_bilinear hB)
    (hom_as_linear S) (linear_id X)))=>i k.
rewrite !hom_as_linearE hS hOrtho (inner_symmetric hC) euclidean_inner_basis hP hDual.
reflexivity.
Qed.

(** Source for [analytic_prefix_projection_orthogonal]: the
    original projection has precisely the adjoint-of-isometry
    property used for O*(n,j) in 3.4.8(1), p. 326. *)
Theorem analytic_prefix_projection_orthogonal:
  is_orthogonal_projection B C (hom_as_linear P).
Proof.
exists (hom_as_linear S);split.
- exact:analytic_prefix_inclusion_orthogonal.
- exact:analytic_prefix_projection_adjoint.
Qed.
End OrthogonalPrefix.

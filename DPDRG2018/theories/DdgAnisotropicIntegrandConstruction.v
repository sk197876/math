(** De Philippis, De Rosa and Ghiraldin (2018), (A.3), p. 1143, and
    DPGPR blueprint def:BF and mr:integrands. Private construction layer
    of B_F, imported only by DdgAnisotropicIntegrandSealed.v: existence of
    B_F(T) for
    T ∈ G(n, d) and an integrand F : G(n, d) → R which is differentiable
    at T relative to G(n, d) in the sense of Federer 3.1.22, p. 235, in
    particular for F of class 1 relative to G(n, d). If u is the gradient
    of the ambient differential D of an extension of F at T, Federer 3.1.1,
    p. 209, then

        B = F(T) T + T^⊥ ∘ (u + u^* ) ∘ T

    satisfies B • L = F(T) (T • L) + D(T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* ) for
    every L ∈ Hom(R^n, R^n). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  HilbertFormCompactness RealNormUP PartialFunctionUP TangentConeUP NormDifferentialUP
  NormClassOneUP NormRegularity RelativeClassUP RelativeDifferentialUP
  RelativeDifferentialRestriction DifferentialGradientUP DifferentialGradient
  HomCompositionDeterminant.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgLemmaA1 DdgGrassmannTangent DdgHomInner
  DdgAnisotropicIntegrandUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AnisotropicIntegrandConstruction.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation G := (orthogonal_projectors R n d).

(** Source for [ddg_hom_gradient_space]: Federer 3.1.1, p. 209, first
    alternative: Hom(R^n, R^n) with the inner product of Federer 1.7.9 is
    finite dimensional, by the base of Federer 1.1.2 and 2.7.16. Supporting
    lemma. *)
Lemma ddg_hom_gradient_space : differential_gradient_space (hom_inner_productP hBn hBn hbn).
Proof. by left; do 2 eexists; exact: (hom_rank_one_baseP hbn hbn). Qed.

(** Source for [ddg_B_exists]: DDG (A.3), p. 1143, and DPGPR def:BF:
    if T ∈ G(n, d) and F is differentiable at T relative to G(n, d), then
    B_F(T) exists. Direct formalisation; the formula
    B = F(T) T + T^⊥ ∘ (u + u^* ) ∘ T, with u the gradient of the ambient
    differential, is new. *)
Theorem ddg_B_exists (F : Hom Rn Rn -> R) (T : Hom Rn Rn) :
  G T -> ddg_relative_differentiable_at d F T -> exists B, is_ddg_B d F T B.
Proof.
move=> hT [Lp hLp].
have hLp0 := hLp.
case: hLp0=> _ [U [g [D [hD [_ hres]]]]].
pose u := norm_gradient ddg_hom_gradient_space hD.
have hu v : D v = HI v u := norm_gradient_pairing ddg_hom_gradient_space hD v.
exists (F T *: T + hom_comp (ddg_perp T) (hom_comp (u + adjL u) T)).
exists Lp; split=> // L.
apply/hres; split; first exact: ddg_tangent_direction_tangent hT L.
rewrite hu /ddg_tangent_direction.
set X := hom_comp (ddg_perp T) (hom_comp L T).
have hbil := inner_bilinear (hom_inner_productP hBn hBn hbn).
have hX : hom_comp (hom_comp (ddg_perp T) L) T = X by apply: hom_ext=> x; rewrite !hom_compE.
rewrite [in RHS](bilDl hbil) [in RHS](inner_scalel (hom_inner_productP hBn hBn hbn)).
rewrite [in RHS]addrAC [in RHS]subrr [in RHS]add0r.
rewrite (ddg_hom_inner_compl (ddg_perp T) (hom_comp (u + adjL u) T) L).
rewrite (ddg_hom_inner_compr (u + adjL u) T).
rewrite (ddg_perp_adjoint hT) (ddg_projector_adjoint hT) hX.
rewrite !(bilDl hbil) ddg_hom_inner_adjointl.
by rewrite (ddg_hom_inner_sym u X) (ddg_hom_inner_sym (adjL u) X).
Qed.

(** Source for [ddg_B_exists_class_one]: DPGPR def:BF and mr:integrands:
    if F is of class 1 relative to G(n, d), then B_F(T) exists for every
    T ∈ G(n, d). Direct formalisation. *)
Theorem ddg_B_exists_class_one (F : Hom Rn Rn -> R) (T : Hom Rn Rn) :
  G T -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  exists B, is_ddg_B d F T B.
Proof. by move=> hT hF; apply: ddg_B_exists=> //; exact: ddg_relative_differentiable. Qed.

End AnisotropicIntegrandConstruction.

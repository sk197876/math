(** De Philippis, De Rosa and Ghiraldin (2018), (A.3), p. 1143, and
    Definition 1.1; De Philippis, Gennaioli, Pigati and Rindler, blueprint
    def:BF, for an integrand F not depending on the point. For T ∈ G(n, d)
    the map B_F(T) ∈ Hom(R^n, R^n) is characterised by

        B_F(T) • L = F(T) (T • L) + D F(T)(T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* )

    for L ∈ Hom(R^n, R^n), where D F(T) is the differential of F at T
    relative to G(n, d) in the sense of Federer 3.1.22, p. 235; its domain
    is Tan(G(n, d), T), which contains the argument by
    [ddg_tangent_direction_tangent]. This file contains the characterising
    predicate, its uniqueness, and the differentiability of integrands of
    class 1; existence is in DdgAnisotropicIntegrandConstruction.v, the
    selected value in DdgAnisotropicIntegrandSealed.v and the public
    interface in DdgAnisotropicIntegrand.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  HilbertFormCompactness RealNormUP PartialFunctionUP TangentConeUP NormDifferentialUP
  NormClassOneUP NormRegularity RelativeClassUP RelativeDifferentialUP
  RelativeDifferentialRestriction RelativeDifferentialUniqueness.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgLemmaA1 DdgHomInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AnisotropicIntegrand.
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
Local Notation G := (orthogonal_projectors R n d).

(** Source for [ddg_relative_differentiable_at]: Federer 3.1.22, p. 235:
    F is differentiable at T relative to G(n, d), with Hom(R^n, R^n)
    normed as in Allard 2.2. Definition. *)
Definition ddg_relative_differentiable_at (F : Hom Rn Rn -> R) (T : Hom Rn Rn) : Prop :=
  @relative_norm_differentiable_at R _ R^o NH N1 hNH G G F T.

(** Source for [is_ddg_B]: DDG (A.3), p. 1143, and DPGPR def:BF for an
    integrand F : G(n, d) → R not depending on the point: B ∈ Hom(R^n, R^n)
    satisfies B • L = F(T) (T • L) + D F(T)(T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* )
    for every L, where D F(T) is a differential of F at T relative to
    G(n, d), Federer 3.1.22, p. 235. The values of F off G(n, d) play no
    role. Definition. *)
Definition is_ddg_B (F : Hom Rn Rn -> R) (T B : Hom Rn Rn) : Prop :=
  exists Lp : partial_function (Hom Rn Rn) R^o,
    @has_relative_norm_differential R _ R^o NH (fun t : R^o => `|t|) hNH G G F T Lp /\
    forall L : Hom Rn Rn,
      partial_function_graph Lp (ddg_tangent_direction T L) (HI B L - F T * HI T L).

(** Source for [ddg_B_unique]: DDG (A.3), p. 1143: B_F(T) is determined
    by its inner products with all L ∈ Hom(R^n, R^n); the relative
    differential is unique by Federer 3.1.22, p. 235. Direct
    formalisation. *)
Theorem ddg_B_unique (F : Hom Rn Rn -> R) (T B B' : Hom Rn Rn) :
  is_ddg_B F T B -> is_ddg_B F T B' -> B = B'.
Proof.
move=> [Lp [hLp hB]] [Lp' [hLp' hB']].
have e := relative_norm_differential_unique (@scalar_absolute_value_norm R) hLp hLp'.
rewrite -e in hB'.
apply: (inner_vectors_ext (hom_inner_productP hBn hBn hbn))=> L.
have h := partial_function_single_valued (hB L) (hB' L).
have h2 : HI B L = HI B' L by move/addIr: h.
by rewrite (ddg_hom_inner_sym L B) (ddg_hom_inner_sym L B') h2.
Qed.

(** Source for [ddg_relative_differentiable]: Federer 3.1.22, p. 235, and
    DPGPR mr:integrands: an integrand of class 1 relative to G(n, d) is
    differentiable relative to G(n, d) at every T ∈ G(n, d). Supporting
    lemma. *)
Lemma ddg_relative_differentiable (F : Hom Rn Rn -> R) (T : Hom Rn Rn) :
  G T -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  ddg_relative_differentiable_at F T.
Proof.
move=> hT hF.
have [U [g [hTU [hg hag]]]] := hF T hT.
have [Df hDf] := (norm_class_firstP hNH hN1 U g).1 hg.
have hD := norm_class_one_differential hDf hTU.
have [Lp hLp] := tangent_differential_restriction_exists NH G T (Df T).
exists Lp; split; first exact: subset_closure.
by exists U, g, (Df T).
Qed.

End AnisotropicIntegrand.

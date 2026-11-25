(** De Philippis, De Rosa and Ghiraldin (2018), (A.3), p. 1143, and
    Definition 1.1; DPGPR blueprint def:BF, for an integrand F not
    depending on the point. Public interface of B_F(T) ∈ Hom(R^n, R^n) and
    C_F(T) = B_F(T) - F(T) T: for T ∈ G(n, d) and F differentiable at T
    relative to G(n, d), Federer 3.1.22, p. 235,

        B_F(T) • L = F(T) (T • L) + D F(T)(T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* )

    for L ∈ Hom(R^n, R^n), where D F(T) is the relative differential, a
    partial function with domain Tan(G(n, d), T). Only the laws of the
    sealed module DdgAnisotropicIntegrandSealed.v are used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm LinearBasis Bilinear Hom
  HomInner GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  EuclideanRectangularAdjoint HilbertFormCompactness RealNormUP PartialFunctionUP
  TangentConeUP RelativeClassUP RelativeDifferentialUP RelativeDifferentialUniqueness.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgLemmaA1 DdgGrassmannTangent
  DdgAnisotropicIntegrandUP DdgAnisotropicIntegrandSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AnisotropicIntegrandInterface.
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

(** Source for [ddg_B]: B_F(T) of DDG (A.3), p. 1143, and DPGPR def:BF,
    for an integrand F : G(n, d) → R not depending on the point.
    Definition. *)
Definition ddg_B (F : Hom Rn Rn -> R) (T : Hom Rn Rn) : Hom Rn Rn := @DdgB.value R n d F T.

(** Source for [ddg_C]: C_F(T) = B_F(T) - F(T) T, DPGPR def:BF.
    Definition. *)
Definition ddg_C (F : Hom Rn Rn -> R) (T : Hom Rn Rn) : Hom Rn Rn := ddg_B F T - F T *: T.

(** Source for [ddg_B_spec]: DDG (A.3), p. 1143, and DPGPR def:BF:
    B_F(T) satisfies the characterising equation whenever T ∈ G(n, d) and F
    is differentiable at T relative to G(n, d). Direct formalisation. *)
Theorem ddg_B_spec (F : Hom Rn Rn -> R) (T : Hom Rn Rn) :
  G T -> @relative_norm_differentiable_at R _ R^o NH N1 hNH G G F T ->
  is_ddg_B d F T (ddg_B F T).
Proof. exact: DdgB.laws. Qed.

(** Source for [ddg_B_characterisation]: DDG (A.3), p. 1143: under the
    hypotheses of [ddg_B_spec], B_F(T) is the only solution of the
    characterising equation. Direct formalisation. *)
Theorem ddg_B_characterisation (F : Hom Rn Rn -> R) (T B : Hom Rn Rn) :
  G T -> @relative_norm_differentiable_at R _ R^o NH N1 hNH G G F T ->
  (is_ddg_B d F T B <-> B = ddg_B F T).
Proof.
move=> hT hF; split=> [hB|->]; last exact: ddg_B_spec.
exact: ddg_B_unique hB (ddg_B_spec hT hF).
Qed.

(** Source for [ddg_B_formula]: DPGPR def:BF, displayed formula, with
    D F(T) any differential of F at T relative to G(n, d) in the sense of
    Federer 3.1.22, p. 235: the pair
    (T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^*, B_F(T) • L - F(T) (T • L)) belongs to
    the graph of D F(T) for every L ∈ Hom(R^n, R^n). Direct
    formalisation. *)
Theorem ddg_B_formula (F : Hom Rn Rn -> R) (T : Hom Rn Rn) (Lp : partial_function (Hom Rn Rn) R^o)
    (L : Hom Rn Rn) :
  G T -> @has_relative_norm_differential R _ R^o NH N1 hNH G G F T Lp ->
  partial_function_graph Lp (ddg_tangent_direction T L) (HI (ddg_B F T) L - F T * HI T L).
Proof.
move=> hT hLp.
have [Lp' [hLp' hB]] := ddg_B_spec hT (ex_intro _ Lp hLp).
by rewrite (relative_norm_differential_unique hN1 hLp hLp').
Qed.

(** Source for [ddg_B_class_one]: DPGPR def:BF and mr:integrands: if F
    is of class 1 relative to G(n, d), Federer 3.1.22, p. 236, then B_F(T)
    satisfies the characterising equation for every T ∈ G(n, d). Direct
    formalisation. *)
Theorem ddg_B_class_one (F : Hom Rn Rn -> R) (T : Hom Rn Rn) :
  G T -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 -> is_ddg_B d F T (ddg_B F T).
Proof. by move=> hT hF; apply: ddg_B_spec=> //; exact: ddg_relative_differentiable. Qed.

End AnisotropicIntegrandInterface.

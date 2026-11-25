(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:MS: the first variation δ_F V ∈ D'(R^n, R^n) of a varifold V
    with respect to an integrand F, as a linear map
    [dgpr_first_variation_functional V F] of the test space
    D(R^n, R^n) into R.

    If V is a varifold with ‖V‖(R^n) < ∞ and F is of class 1 relative
    to G(n, k), then δ_F V(g) is the derivative at t = 0 of the
    anisotropic energy of [x ↦ x + t g(x)]_# V for every
    g ∈ D(R^n, R^n) ([dgpr_first_variation_functional_specification]),
    and δ_F V(g) = ∫ B_F(S) • Dg(x) dV(x, S)
    ([dgpr_first_variation_functional_representation]). In particular,
    for an integrand F in the sense of def:BF ([dgpr_integrand]), the
    functional satisfies the hypothesis on S of the section MichaelSimon
    of DgprMichaelSimon.v ([dgpr_first_variation_functional_variation]).
    The functional is chosen in DgprFirstVariationFunctionalSealed.v;
    this file uses only its laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormMetric NormDifferentialUP RelativeClassUP PartialFunctionUP MeasureUP
  MeasureIntegralUP SummableRealFunctionUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds.
From DPGPR Require Import DgprAnisotropicIntegrand DgprFirstVariation
  DgprFirstVariationFunctionalUP DgprFirstVariationFunctionalSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FirstVariationFunctional.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GB := (grassmann_bundle R n k).
Variable E : lmodType R.
Variable ev : E -> Rn -> Rn.
Hypothesis hE : is_smooth_function_space hNn hNn setT ev.
Local Notation DT := (smooth_test_space hE).
Local Notation tv := (smooth_test_value hE).

(** Source for [dgpr_first_variation_functional]: blueprint thm:MS, the
    first variation δ_F V ∈ D'(R^n, R^n) of V with respect to F, through
    the sealed choice of DgprFirstVariationFunctionalSealed.v.
    Definition. *)
Definition dgpr_first_variation_functional (V : set GB -> \bar R) (F : Hom Rn Rn -> R) :
    Hom DT R^o :=
  @DgprFirstVariationFunctional.value R n k E ev hE V F.

(** Source for [dgpr_first_variation_functional_specification]:
    blueprint thm:MS and lem:first_variation: if V is a varifold with
    ‖V‖(R^n) < ∞ and F is of class 1 relative to G(n, k), then
    δ_F V(g) is the first variation of V with respect to F along g for
    every g ∈ D(R^n, R^n). *)
Theorem dgpr_first_variation_functional_specification (V : set GB -> \bar R)
    (F : Hom Rn Rn -> R) :
  is_varifold V -> (V setT < +oo)%E -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  is_dgpr_first_variation_functional V F (dgpr_first_variation_functional V F).
Proof. exact: DgprFirstVariationFunctional.laws. Qed.

(** Source for [dgpr_first_variation_functional_variation]: blueprint
    thm:MS: for a varifold V with ‖V‖(R^n) < ∞ and an integrand F
    ([dgpr_integrand], def:BF), the functional S = δ_F V satisfies
    S(g) = δ_F V(g) for every g ∈ D(R^n, R^n) and its differentials Dg;
    this is the hypothesis on S of the section MichaelSimon of
    DgprMichaelSimon.v. *)
Theorem dgpr_first_variation_functional_variation (V : set GB -> \bar R) (F : Hom Rn Rn -> R) :
  is_varifold V -> (V setT < +oo)%E -> dgpr_integrand k F ->
  forall (g : DT) (Dg : Rn -> Hom Rn Rn),
    (forall x, has_norm_differential Nn Nn setT (tv g) x (Dg x)) ->
    is_dgpr_first_variation V F (tv g) Dg (dgpr_first_variation_functional V F g).
Proof.
move=> hV hVf hF g Dg hD.
exact: (dgpr_first_variation_functional_specification hV hVf hF.1 hD).
Qed.

(** Source for [dgpr_first_variation_functional_representation]:
    blueprint lem:first_variation: if V is a varifold with
    ‖V‖(R^n) < ∞ and F is of class 1 relative to G(n, k), then
        δ_F V(g) = ∫ B_F(S) • Dg(x) dV(x, S)
    for g ∈ D(R^n, R^n) and its differentials Dg. *)
Theorem dgpr_first_variation_functional_representation (V : set GB -> \bar R)
    (F : Hom Rn Rn -> R) (g : DT) (Dg : Rn -> Hom Rn Rn) :
  is_varifold V -> (V setT < +oo)%E -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  (forall x, has_norm_differential Nn Nn setT (tv g) x (Dg x)) ->
  is_measure_integral V
    (real_total_integrand (fun z : GB => HI (dgpr_B k F (set_val z.2 : Hom Rn Rn)) (Dg z.1)))
    (dgpr_first_variation_functional V F g)%:E.
Proof.
move=> hV hVf hF hD.
exact: (dgpr_first_variation_functional_integral hV hVf hF
  (dgpr_first_variation_functional_specification hV hVf hF) hD).
Qed.

End FirstVariationFunctional.

(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:MS: the predicate characterising the first variation
    δ_F V ∈ D'(R^n, R^n) of a varifold V with respect to an integrand F,
    as a linear functional on the test space D(R^n, R^n).

    A linear map S : D(R^n, R^n) → R is the first variation of V with
    respect to F if, for every g ∈ D(R^n, R^n), with differentials Dg(x)
    for x ∈ R^n, the number S(g) is δ_F V(g) in the sense of
    [is_dgpr_first_variation] (DgprFirstVariation.v), the derivative at
    t = 0 of the anisotropic energy of the image varifolds
    [x ↦ x + t g(x)]_# V. Such S is unique
    ([dgpr_first_variation_functional_unique]). If V is a varifold with
    ‖V‖(R^n) < ∞ and F is of class 1 relative to G(n, k), then
        S(g) = ∫ B_F(S') • Dg(x) dV(x, S')
    ([dgpr_first_variation_functional_integral]), by lem:first_variation.
    The existence of S is proved in
    DgprFirstVariationFunctionalConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity
  RelativeClassUP PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds.
From DPGPR Require Import DgprAnisotropicIntegrand DgprFirstVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FirstVariationFunctionalUP.
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

(** Source for [is_dgpr_first_variation_functional]: blueprint thm:MS,
    the distribution δ_F V ∈ D'(R^n, R^n), with lem:first_variation and
    Federer 4.1.1, p. 346: S(g) = δ_F V(g) for every g ∈ D(R^n, R^n) and
    its differentials Dg. Definition. *)
Definition is_dgpr_first_variation_functional (V : set GB -> \bar R) (F : Hom Rn Rn -> R)
    (S : Hom DT R^o) : Prop :=
  forall (g : DT) (Dg : Rn -> Hom Rn Rn),
    (forall x, has_norm_differential Nn Nn setT (tv g) x (Dg x)) ->
    is_dgpr_first_variation V F (tv g) Dg (S g).

(** Source for [dgpr_test_differential_exists]: Federer 4.1.1, p. 344,
    and 3.1.1, p. 210: every g ∈ D(R^n, R^n) has a differential Dg(x) at
    each x ∈ R^n. Supporting lemma. *)
Lemma dgpr_test_differential_exists (g : DT) :
  exists Dg : Rn -> Hom Rn Rn, forall x, has_norm_differential Nn Nn setT (tv g) x (Dg x).
Proof.
have [D0 hD0] := (norm_class_firstP hNn hNn setT (tv g)).1 (smooth_test_value_smooth hE g 1%N).
by exists D0 => x; exact: (norm_class_one_differential hD0 (Logic.I : setT x)).
Qed.

(** Source for [dgpr_first_variation_functional_unique]: blueprint
    thm:MS, with Federer 2.9.19, p. 163: the first variation δ_F V is
    unique as a linear functional ([dgpr_first_variation_unique]).
    Supporting lemma. *)
Lemma dgpr_first_variation_functional_unique (V : set GB -> \bar R) (F : Hom Rn Rn -> R)
    (S S' : Hom DT R^o) :
  is_dgpr_first_variation_functional V F S -> is_dgpr_first_variation_functional V F S' -> S = S'.
Proof.
move=> h h'; apply: hom_ext => g.
have [Dg hD] := dgpr_test_differential_exists g.
exact: dgpr_first_variation_unique (h g Dg hD) (h' g Dg hD).
Qed.

(** Source for [dgpr_first_variation_functional_integral]: blueprint
    lem:first_variation: if V is a varifold with ‖V‖(R^n) < ∞, F is of
    class 1 relative to G(n, k) and S is the first variation of V with
    respect to F, then S(g) = ∫ B_F(S') • Dg(x) dV(x, S') for
    g ∈ D(R^n, R^n) ([dgpr_first_variation]). Supporting lemma. *)
Lemma dgpr_first_variation_functional_integral (V : set GB -> \bar R) (F : Hom Rn Rn -> R)
    (S : Hom DT R^o) (g : DT) (Dg : Rn -> Hom Rn Rn) :
  is_varifold V -> (V setT < +oo)%E -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  is_dgpr_first_variation_functional V F S ->
  (forall x, has_norm_differential Nn Nn setT (tv g) x (Dg x)) ->
  is_measure_integral V
    (real_total_integrand (fun z : GB => HI (dgpr_B k F (set_val z.2 : Hom Rn Rn)) (Dg z.1)))
    (S g)%:E.
Proof.
move=> hV hVf hF hS hD.
have [c [hc hI]] := dgpr_first_variation hV hVf hF hD.
by rewrite (dgpr_first_variation_unique (hS g Dg hD) hc).
Qed.

End FirstVariationFunctionalUP.

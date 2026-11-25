(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:MS: private existence proof for the first variation
    δ_F V ∈ D'(R^n, R^n) of a varifold V with ‖V‖(R^n) < ∞ with respect
    to an integrand F of class 1 relative to G(n, k).

    For g ∈ D(R^n, R^n) let Dg be its differential, which is unique
    (Federer 3.1.1) and depends linearly on g (3.1.11). By
    lem:first_variation ([dgpr_first_variation]) the function
    [(x, S') ↦ B_F(S') • Dg(x)] is V summable and its integral is
    δ_F V(g); the integral is linear in g
    ([real_integral_linear_map_exists]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom Bilinear
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner
  RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional NormDifferentialArithmetic
  NormClassOneUP NormRegularity RelativeClassUP PartialFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP RealIntegralLinearMapExistence
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds.
From DPGPR Require Import DgprAnisotropicIntegrand DgprFirstVariation
  DgprFirstVariationFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FirstVariationFunctionalConstruction.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hH).
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

(** Source for [dgpr_first_variation_functional_exists]: blueprint
    thm:MS and lem:first_variation, with Federer 4.1.1, p. 346: if V is
    a varifold with ‖V‖(R^n) < ∞ and F is of class 1 relative to
    G(n, k), then [g ↦ ∫ B_F(S') • Dg(x) dV(x, S')] is a linear map
    S : D(R^n, R^n) → R which is the first variation of V with respect
    to F. Private existence proof. *)
Theorem dgpr_first_variation_functional_exists (V : set GB -> \bar R) (F : Hom Rn Rn -> R) :
  is_varifold V -> (V setT < +oo)%E -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  exists S : Hom DT R^o, is_dgpr_first_variation_functional V F S.
Proof.
move=> hV hVf hF.
have [Dsel hDsel] := choice (@dgpr_test_differential_exists R n E ev hE).
have hlin (a : R) (g h : DT) (x : Rn) : Dsel (a *: g + h) x = a *: Dsel g x + Dsel h x.
  have hd : has_norm_differential Nn Nn setT (tv (a *: g + h)) x (a *: Dsel g x + Dsel h x).
    have -> : tv (a *: g + h) = (fun y => a *: tv g y + tv h y).
      apply: funext => y.
      exact: (congr1 (fun q : Rn -> Rn => q y) (smooth_test_values_linear hE a g h)).
    exact: (norm_differential_add hNn (norm_differential_scale hNn hNn a (hDsel g x)) (hDsel h x)).
  exact: (norm_differential_unique hNn hNn (hDsel (a *: g + h) x) hd).
pose Fz (g : DT) (z : GB) := HI (dgpr_B k F (set_val z.2 : Hom Rn Rn)) (Dsel g z.1).
have hFz (a : R) (g h : DT) (z : GB) : Fz (a *: g + h) z = a * Fz g z + Fz h z.
  by rewrite /Fz hlin (bilDr (inner_bilinear hH)) (bilZr (inner_bilinear hH)).
have hFin (g : DT) : exists c : R, is_measure_integral V (real_total_integrand (Fz g)) c%:E.
  have [c [_ hI]] := dgpr_first_variation hV hVf hF (hDsel g).
  by exists c.
have [S hS] := @real_integral_linear_map_exists R GB DT V (varifold_measure hV) Fz hFz hFin.
exists S => g Dg hD.
have -> : Dg = Dsel g.
  apply: funext => x; exact: (norm_differential_unique hNn hNn (hD x) (hDsel g x)).
have [c [hc hI]] := dgpr_first_variation hV hVf hF (hDsel g).
have e : S g = c := congr1 (@fine R) (measure_integral_unique (hS g) hI).
by rewrite e.
Qed.

End FirstVariationFunctionalConstruction.

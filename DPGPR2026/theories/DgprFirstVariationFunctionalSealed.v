(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:MS: the opaque first variation δ_F V ∈ D'(R^n, R^n) of a
    varifold V with respect to an integrand F. The choice of the linear
    functional remains private; only its laws are exported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm LinearBasis Hom GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness HomInner RealNormUP
  RelativeClassUP SmoothFunctionSpaceUP SmoothTestSpaces.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds.
From DPGPR Require Import DgprFirstVariationFunctionalUP DgprFirstVariationFunctionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type DgprFirstVariationFunctionalSignature.
(** Source for [value]: blueprint thm:MS, the first variation
    δ_F V ∈ D'(R^n, R^n) of V with respect to F. *)
Parameter value : forall (R : realType) (n k : nat) (E : lmodType R) (ev : E -> R_n R n -> R_n R n)
  (hE : is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT ev),
  (set (grassmann_bundle R n k) -> \bar R) -> (Hom (R_n R n) (R_n R n) -> R) ->
  Hom (smooth_test_space hE) R^o.
(** Source for [laws]: blueprint thm:MS and lem:first_variation: if V
    is a varifold with ‖V‖(R^n) < ∞ and F is of class 1 relative to
    G(n, k), then [value] is the first variation of V with respect to F. *)
Parameter laws : forall (R : realType) (n k : nat) (E : lmodType R) (ev : E -> R_n R n -> R_n R n)
  (hE : is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT ev)
  (V : set (grassmann_bundle R n k) -> \bar R) (F : Hom (R_n R n) (R_n R n) -> R),
  is_varifold V -> (V setT < +oo)%E ->
  @norm_class_relative R _ R^o (hom_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
    (@coordinate_basisP R n)) (fun t : R^o => `|t|)
    (inner_norm_real_norm (hom_inner_productP (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n)))
    (@scalar_absolute_value_norm R) (orthogonal_projectors R n k) (orthogonal_projectors R n k) F 1 ->
  is_dgpr_first_variation_functional V F (@value R n k E ev hE V F).
End DgprFirstVariationFunctionalSignature.

Module DgprFirstVariationFunctional : DgprFirstVariationFunctionalSignature.
(** Source for [value]: private choice of the first variation of
    blueprint thm:MS when it exists, and 0 otherwise. *)
Definition value (R : realType) (n k : nat) (E : lmodType R) (ev : E -> R_n R n -> R_n R n)
    (hE : is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT ev)
    (V : set (grassmann_bundle R n k) -> \bar R) (F : Hom (R_n R n) (R_n R n) -> R) :
    Hom (smooth_test_space hE) R^o :=
  match pselect (exists S, is_dgpr_first_variation_functional V F S) with
  | left h => sval (constructive_indefinite_description h)
  | right _ => 0
  end.
(** Source for [laws]: the chosen functional is the first variation of
    blueprint thm:MS whenever lem:first_variation applies. *)
Lemma laws (R : realType) (n k : nat) (E : lmodType R) (ev : E -> R_n R n -> R_n R n)
    (hE : is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT ev)
    (V : set (grassmann_bundle R n k) -> \bar R) (F : Hom (R_n R n) (R_n R n) -> R) :
  is_varifold V -> (V setT < +oo)%E ->
  @norm_class_relative R _ R^o (hom_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
    (@coordinate_basisP R n)) (fun t : R^o => `|t|)
    (inner_norm_real_norm (hom_inner_productP (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n)))
    (@scalar_absolute_value_norm R) (orthogonal_projectors R n k) (orthogonal_projectors R n k) F 1 ->
  is_dgpr_first_variation_functional V F (@value R n k E ev hE V F).
Proof.
move=> hV hVf hF; rewrite /value; case: pselect => [h|h].
  exact: (svalP (constructive_indefinite_description h)).
by exfalso; apply: h; exact: dgpr_first_variation_functional_exists.
Qed.
End DgprFirstVariationFunctional.

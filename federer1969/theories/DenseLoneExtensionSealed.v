(** Federer (1969), 2.5.14, p. 108: norm-one L1 extension for the Radon
    component argument, through the existing is_dominated_lone_extension
    specification. Positive density replaces the stronger regularity input
    of 2.5.9. Source context and existence proof:
    DenseLoneExtensionConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP ScalarLipschitzExtensionUP FunctionSeminormDistance TotalScalarLpUP TotalScalarLpFiniteSeminorm
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  DominatedLoneExtensionUP DenseLoneExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type DenseLoneExtensionSignature.
(** Source for [value]: abstract norm-one linear extension
    in Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Parameter value : forall (R : realType) (X : choiceType)
  (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
  (mu : set X -> \bar R) (hm : is_measure mu),
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  L (fun _ => 0%R) -> is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) -> is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) -> (X -> R) -> R.
(** Source for [laws]: verified extension specification for
    Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Parameter laws : forall (R : realType) (X : choiceType)
  (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
  (hL0 : L (fun _ => 0%R)) (hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1))) (hA : is_daniell_integral L A)
  (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R),
  is_dominated_lone_extension mu L A (@value R X L hL F A mu hm hF hrep hL0 hdense hA hb).
End DenseLoneExtensionSignature.
Module DenseLoneExtension : DenseLoneExtensionSignature.
(** Source for [value]: private witness selection for the
    linear extension in Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Definition value (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R)) (hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1))) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :=
  projT1 (cid (@dense_dominated_lone_extension_exists R X L hL F A mu hm hF hrep hL0 hdense hA hb)).
(** Source for [laws]: the selected extension satisfies its
    proved laws, supporting Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Lemma laws (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R)) (hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1))) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :
  is_dominated_lone_extension mu L A (@value R X L hL F A mu hm hF hrep hL0 hdense hA hb).
Proof. exact: projT2 (cid (@dense_dominated_lone_extension_exists R X L hL F A mu hm hF hrep hL0 hdense hA hb)). Qed.
End DenseLoneExtension.

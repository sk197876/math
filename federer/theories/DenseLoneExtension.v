(** Federer (1969), 2.5.14, p. 108: norm-one L1 extension for the Radon
    component argument, through the existing is_dominated_lone_extension
    specification. Positive density replaces the stronger regularity input
    of 2.5.9. Source context and existence proof:
    DenseLoneExtensionConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP ScalarLipschitzExtensionUP FunctionSeminormDistance TotalScalarLpUP TotalScalarLpFiniteSeminorm
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  DominatedLoneExtensionUP DenseLoneExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dense_lone_extension]: the extension mu_1
    used in Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Definition dense_lone_extension (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R)) (hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1))) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :=
  @DenseLoneExtension.value R X L hL F A mu hm hF hrep hL0 hdense hA hb.

(** Source for [dense_lone_extension_specification]: linearity,
    agreement, and unit norm bound in Federer 2.5.14, p. 108, by the extension argument of 2.5.9, p. 100. *)
Lemma dense_lone_extension_specification (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R)) (hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1))) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :
  is_dominated_lone_extension mu L A (@dense_lone_extension R X L hL F A mu hm hF hrep hL0 hdense hA hb).
Proof. exact: (@DenseLoneExtension.laws R X L hL F A mu hm hF hrep hL0 hdense hA hb). Qed.

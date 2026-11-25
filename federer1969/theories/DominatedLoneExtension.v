(** Public norm-one extension for Federer (1969), 2.5.9, p. 100. Source
    context: DominatedLoneExtensionUP.v. This interface exports only the
    selected function and its laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  DominatedLoneExtensionUP DominatedLoneExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_lone_extension]: the extension mu_1
    used in Federer 2.5.9, p. 100. *)
Definition dominated_lone_extension (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hr : is_function_lattice_regular L mu) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :=
  @DominatedLoneExtension.value R X L hL F A mu hm hF hrep hr hA hb.

(** Source for [dominated_lone_extension_specification]: linearity,
    agreement, and unit norm bound in Federer 2.5.9, p. 100. *)
Lemma dominated_lone_extension_specification (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hr : is_function_lattice_regular L mu) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :
  is_dominated_lone_extension mu L A (@dominated_lone_extension R X L hL F A mu hm hF hrep hr hA hb).
Proof. exact: (@DominatedLoneExtension.laws R X L hL F A mu hm hF hrep hr hA hb). Qed.

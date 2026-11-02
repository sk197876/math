(** Sealed extension for Federer (1969), 2.5.9, p. 100. Source context and
    the corrected positive-density route are recorded in
    DominatedLoneExtensionConstruction.v. Only linearity, agreement, and the
    norm bound are exposed downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  DominatedLoneExtensionUP DominatedLoneExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type DominatedLoneExtensionSignature.
(** Source for [value]: abstract norm-one linear extension
    in Federer 2.5.9, p. 100. *)
Parameter value : forall (R : realType) (X : choiceType)
  (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
  (mu : set X -> \bar R) (hm : is_measure mu),
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) -> (X -> R) -> R.
(** Source for [laws]: verified extension specification for
    Federer 2.5.9, p. 100. *)
Parameter laws : forall (R : realType) (X : choiceType)
  (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
  (hr : is_function_lattice_regular L mu) (hA : is_daniell_integral L A)
  (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R),
  is_dominated_lone_extension mu L A (@value R X L hL F A mu hm hF hrep hr hA hb).
End DominatedLoneExtensionSignature.
Module DominatedLoneExtension : DominatedLoneExtensionSignature.
(** Source for [value]: private witness selection for the
    linear extension in Federer 2.5.9, p. 100. *)
Definition value (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hr : is_function_lattice_regular L mu) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :=
  projT1 (cid (@dominated_lone_extension_exists R X L hL F A mu hm hF hrep hr hA hb)).
(** Source for [laws]: the selected extension satisfies its
    proved laws, supporting Federer 2.5.9, p. 100. *)
Lemma laws (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hF : is_monotone_daniell_integral L F) (hrep : is_real_integral_functional mu L F)
    (hr : is_function_lattice_regular L mu) (hA : is_daniell_integral L A)
    (hb : forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) :
  is_dominated_lone_extension mu L A (@value R X L hL F A mu hm hF hrep hr hA hb).
Proof. exact: projT2 (cid (@dominated_lone_extension_exists R X L hL F A mu hm hF hrep hr hA hb)). Qed.
End DominatedLoneExtension.

(** Opaque assignment of the integral functional in Federer (1969), 2.5.1,
    p. 92 Only the defining integral laws are exposed. Source conventions:
    RealIntegralFunctionalUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import SummableRealFunctionUP RealIntegralFunctionalUP RealIntegralFunctionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type RealIntegralFunctionalSignature.
(** Source for [value]: the integral map on L in Federer 2.5.1, p. 92 *)
Parameter value : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (L : set (X -> R)), L `<=` summable_real_functions mu -> (X -> R) -> R.
(** Source for [laws]: the integral specification for the map in Federer
    2.5.1, p. 92 *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (L : set (X -> R)) (hL : L `<=` summable_real_functions mu),
  is_real_integral_functional mu L (@value R X mu L hL).
End RealIntegralFunctionalSignature.
Module RealIntegralFunctional : RealIntegralFunctionalSignature.
(** Source for [value]: selection from the existence proof of the integral
    map in Federer 2.5.1, p. 92 *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (L : set (X -> R)) (hL : L `<=` summable_real_functions mu) :=
  projT1 (cid (real_integral_functional_exists hL)).
(** Source for [laws]: the selected map satisfies the integral law in
    Federer 2.5.1, p. 92 *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (L : set (X -> R)) (hL : L `<=` summable_real_functions mu) :
  is_real_integral_functional mu L (@value R X mu L hL).
Proof. exact: projT2 (cid (real_integral_functional_exists hL)). Qed.
End RealIntegralFunctional.

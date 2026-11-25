(** Federer (1969), 4.1.25, p. 383: the
    original full-fibre sum vanishes when all its
    defined terms vanish. This supports the exact
    support-image assertion and the empty and zero-field
    boundaries. Undefined summands retain their original
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear CurrentCoefficientNorms
  CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP
  PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed
  PartialFibreNumericalSum NumericalSum NumericalSumValues NonnegativeSum NonnegativeSumSupport
  CurrentAreaFibreSumUP CurrentAreaFibreSumEvaluations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_fibre_sum_zero]: the
    zero fibre sum implicit in Federer 4.1.25,
    p. 383, when the original field is zero
    on the whole fibre. No countability hypothesis
    on the fibre and no default input value are added. *)
Theorem current_area_fibre_sum_zero (R : realType)
    (h2 : (1+1 : R) != 0) (X : choiceType) n m
    (f : X -> R_n R n)
    (u : partial_function X (exterior_power (R_n R n) m)) y eta :
  @is_current_area_fibre_sum R X n m f u y eta ->
  (forall x v, f x = y -> partial_function_graph u x v -> v = 0) ->
  eta = 0.
Proof.
move=> hSum hZero.
pose w := @PartialFunctionExtension.value X (exterior_power (R_n R n) m) u 0%R.
have hW := @PartialFunctionExtension.laws X (exterior_power (R_n R n) m) u 0%R.
have hWZero x : f x = y -> w x = 0.
  move=> hXY.
  have [v hValue] := @current_area_fibre_sum_input_domain R X n m f u y eta hSum x hXY.
  by rewrite /w (hW x v hValue) (hZero x v hXY hValue).
apply: (continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply: hom_ext => a; rewrite !MultivectorDual.laws.
change (pairing eta a = pairing_left a 0).
rewrite linear0 /=.
have hAt := current_area_fibre_sum_extension_evaluations hW hSum a.
have hEval x : f x = y -> (pairing (w x) a)%:E = (0 : R)%:E.
  move=> hx; rewrite (hWZero x hx).
  change ((pairing_left a 0)%:E = (0 : R)%:E).
  by rewrite linear0.
have hNumerical : numerical_sum [set x | f x = y]
    (fun x => (pairing (w x) a)%:E) = Some (0 : R)%:E.
  rewrite (numerical_sum_ext hEval).
  rewrite numerical_sum_nonnegative; last by move=> x _; exact: lexx.
  by rewrite (nonnegative_sum_zero (fun x (_ : f x = y) => erefl (0 : \bar R))).
have hBoth := eq_trans (esym hAt) hNumerical.
injection hBoth => hPairing.
exact: hPairing.
Qed.

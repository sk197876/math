(** Federer (1969), 4.1.25, p. 383: the original
    vector fibre sum exists on every fibre where all
    original summands are defined and their masses have
    finite sum. The area formula must prove that these
    conditions hold almost everywhere; they are not
    extra hypotheses in the final theorem. A total
    extension used in this proof does not change the
    original partial summand or its domain. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  PartialFunctionUP PartialFunctionPostcomposition PartialFunctionExtensionUP
  PartialFibreNumericalSum NonnegativeSum
  CurrentVectorNumericalSumExistence CurrentAreaFibreSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section AreaFibreExistence.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variable X : choiceType.
Variables n m : nat.
Local Notation Y := (R_n R n).
Local Notation V := (exterior_power Y m).
Local Notation A := (A_m Y R^o m).
Variable f : X -> Y.
Variable u : partial_function X V.

(** Source for [current_area_fibre_sum_exists]: existence
    of the exact full-fibre sum in Federer 4.1.25,
    p. 383, using the signed scalar fibre sums of
    3.2.3(2), p. 243, and the finite actual multivector
    dual. No undefined input is assigned a value. *)
Theorem current_area_fibre_sum_exists (w : X -> V) y :
  is_partial_function_total_extension u w ->
  (forall x, f x = y -> partial_function_domain u x) ->
  nonnegative_sum [set x | f x = y]
    (fun x => (@current_vector_mass R h2 n m (w x))%:E) < +oo ->
  exists eta : V, @is_current_area_fibre_sum R X n m f u y eta.
Proof.
move=> hExtension hDomain hFinite.
have [eta hEta] := @current_vector_numerical_sum_exists R h2 X n m
  [set x | f x = y] w hFinite.
exists eta => a.
apply: (@partial_fibre_numerical_sum_graph R X Y f
  (@current_area_fibre_pairing_integrand R X n m u a)
  y (pairing eta a)%:E).2.
exists (fun x => (pairing (w x) a)%:E); split; last exact: hEta a.
move=> x hx.
have [v hValue] := hDomain x hx.
have hW : partial_function_graph u x (w x).
  by rewrite (hExtension x v hValue).
change (exists v, partial_function_graph u x v /\
  (pairing v a)%:E = (pairing (w x) a)%:E).
exists (w x); by split.
Qed.
End AreaFibreExistence.

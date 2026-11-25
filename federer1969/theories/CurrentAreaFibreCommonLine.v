(** Federer (1969), 4.1.25, p. 383: once
    the preceding geometric argument gives one common
    exterior line for the original full fibre, its
    vector sum has that direction. Positive degree
    gives simplicity, and a nonzero sum gives the
    displayed signed norm-and-direction identity in every
    degree. Keep the literal degree-zero simplicity
    issue separate from these valid algebraic laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading SimpleVectors CurrentCoefficientNorms
  PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed
  CurrentAreaFibreSumUP CurrentAreaFibreSumEvaluations
  CurrentVectorNumericalSumLine NormedProportionalDirection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CommonFibreLine.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable X : choiceType.
Variables n m : nat.
Local Notation Y := (R_n R n).
Local Notation V := (exterior_power Y m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation hM := (@current_vector_mass_real_norm R h2 n m).
Variable f : X -> Y.
Variable u : partial_function X V.
Variables (y : Y) (eta tau : V).
Hypothesis hTau : tau != 0.
Hypothesis hSum : @is_current_area_fibre_sum R X n m f u y eta.
Hypothesis hTermLine : forall x v, f x = y ->
  partial_function_graph u x v -> exists c : R, v = c *: tau.

(** Source for [current_area_fibre_sum_common_line]:
    the actual full vector fibre sum remains on
    the common line of its terms, as used
    in Federer 4.1.25, p. 383. The original
    sum itself supplies every input-domain condition. *)
Theorem current_area_fibre_sum_common_line :
  exists c : R, eta = c *: tau.
Proof.
pose w := @PartialFunctionExtension.value X V u 0%R.
have hW : is_partial_function_total_extension u w :=
  @PartialFunctionExtension.laws X V u 0%R.
apply: (@current_vector_numerical_sum_line R h2 X n m
  [set x | f x = y] w tau eta hTau).
- move=> x hx; have [v hValue] :=
    @current_area_fibre_sum_input_domain R X n m f u y eta hSum x hx.
  rewrite (hW x v hValue); exact: hTermLine x v hx hValue.
- exact: current_area_fibre_sum_extension_evaluations hW hSum.
Qed.

(** Source for [current_area_fibre_sum_positive_simple]:
    the simplicity conclusion of Federer 4.1.25,
    p. 383, in every positive degree, including
    a zero total produced by cancellation. The
    literal empty-product convention is not extended
    silently to arbitrary degree-zero scalars. *)
Theorem current_area_fibre_sum_positive_simple :
  (0 < m)%N -> simple tau -> simple eta.
Proof.
move=> hPositive hSimple.
have [c ->] := current_area_fibre_sum_common_line.
exact: simple_scale hPositive hSimple.
Qed.

(** Source for [current_area_fibre_sum_signed_terms]:
    each original summand is plus or minus its
    mass times the unit direction of the nonzero
    total, as displayed in Federer 4.1.25,
    p. 383. The zero summand and degree-zero
    coefficient space are retained. *)
Theorem current_area_fibre_sum_signed_terms :
  eta != 0 -> forall x v, f x = y ->
    partial_function_graph u x v ->
    exists s : R, (s = 1 \/ s = -1) /\
      v = (s*M v) *: ((M eta)^-1 *: eta).
Proof.
move=> hEta x v hXY hValue.
have [c hEtaValue] := current_area_fibre_sum_common_line.
have hC : c != 0.
  apply/eqP => hZero; move: hEta.
  by rewrite hEtaValue hZero scale0r eqxx.
have [d hVValue] := @hTermLine x v hXY hValue.
have hProportional : v = (d/c) *: eta.
  by rewrite hEtaValue scalerA divfK // -hVValue.
exact: (@normed_proportional_direction R V M hM v eta (d/c) hEta hProportional).
Qed.
End CommonFibreLine.

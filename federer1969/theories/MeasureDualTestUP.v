(** Federer (1969), 2.4.16, pp. 89–90: supremum over conjugate unit-ball
    tests. The erratum, p. 2, book p. 89 line 19, replaces the printed
    equality-one condition by at most one. The sets below retain all defined
    signed integral values in Federer's display; no integral of an undefined
    difference of infinities is silently assigned. Sign matching includes
    equality of the original domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct
  MeasureLpMembershipUP MeasureLpNorm MeasureLinfinityUP MeasureEssentialNorm MeasureIntegralUP ScalarSignTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_lp_unit_test]: the finite-q test ball
    in Federer 2.4.16, p. 89, corrected by the erratum, p. 2,
    book p. 89 line 19. All Lq membership conditions are included. *)
Definition is_finite_lp_unit_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (q : R)
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  is_measure_lp_function mu q u /\ measure_lp_norm mu (fun y : R => `|y|%R) q u <= 1.

(** Source for [is_linfinity_unit_test]: the q=infinity test ball
    in the p=1 case of Federer 2.4.16, p. 89, using the erratum's
    at-most-one normalisation and countable measurability condition. *)
Definition is_linfinity_unit_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  is_measure_linfinity_function mu u /\ measure_essential_norm mu (fun y : R => `|y|%R) u <= 1.

(** Source for [is_sign_matching_test]: sign(u)=sign(f) in
    Federer 2.4.16, p. 89, interpreted as equality of partial sign
    functions, including their domains. Total functions give the printed case. *)
Definition is_sign_matching_test (R : realType) (X : Type)
    (f u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  forall x z, partial_function_graph (partial_scalar_sign f) x z <->
    partial_function_graph (partial_scalar_sign u) x z.

(** Source for [finite_dual_integral_values]: the values in the
    finite-q supremum of Federer 2.4.16, p. 89, with the erratum's
    unit ball. Only defined signed integrals contribute values. *)
Definition finite_dual_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (q : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set (\bar R) :=
  [set z | exists u, is_finite_lp_unit_test mu q u /\
    is_measure_integral mu (partial_scalar_product f u) z].

(** Source for [infinity_dual_integral_values]: the q=infinity
    supremum values in Federer 2.4.16, p. 89, for the p=1 endpoint. *)
Definition infinity_dual_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set (\bar R) :=
  [set z | exists u, is_linfinity_unit_test mu u /\
    is_measure_integral mu (partial_scalar_product f u) z].

(** Source for [sign_matching_finite_dual_values]: the additional
    sign constraint in Federer 2.4.16, p. 89, for finite q. *)
Definition sign_matching_finite_dual_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (q : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set (\bar R) :=
  [set z | exists u, is_finite_lp_unit_test mu q u /\ is_sign_matching_test f u /\
    is_measure_integral mu (partial_scalar_product f u) z].

(** Source for [sign_matching_infinity_dual_values]: the additional
    sign constraint in the p=1 endpoint of Federer 2.4.16, p. 89. *)
Definition sign_matching_infinity_dual_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set (\bar R) :=
  [set z | exists u, is_linfinity_unit_test mu u /\ is_sign_matching_test f u /\
    is_measure_integral mu (partial_scalar_product f u) z].

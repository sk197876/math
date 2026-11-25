(** Federer (1969), 2.4.17, p. 90: the exponent sets P and U and the
    convention 1/0=infinity. The norm family in 2.4.12, p. 86, is defined
    only for 1<=p<=infinity; this domain is explicit below. The family joins
    the two existing sealed norm interfaces; no norm implementation is
    exposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureLpNorm MeasureEssentialNorm
  RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exponent_norm]: the single extended
    exponent family phi_p(f) used in Federer 2.4.17, p. 90,
    joining the two defining formulas of 2.4.12, p. 86. *)
Definition measure_exponent_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (p : \bar R) :=
  match p with
  | EFin q => measure_lp_norm mu (fun y : R => `|y|%R) q f
  | +oo => measure_essential_norm mu (fun y : R => `|y|%R) f
  | -oo => 0
  end.

(** Source for [measure_finite_norm_exponents]: the set P in
    Federer 2.4.17, p. 90, with its inherited domain
    1<=p<=infinity from 2.4.12 made explicit. *)
Definition measure_finite_norm_exponents (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set (\bar R) :=
  [set p | 1 <= p /\ measure_exponent_norm mu f p < +oo].

(** Source for [measure_reciprocal_exponent_norm]: the family
    phi_(1/u)(f) in Federer 2.4.17, p. 90, using the
    printed convention 1/0=infinity. Only 0<=u<=1 is relevant. *)
Definition measure_reciprocal_exponent_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (u : R) :=
  if u == 0%R then measure_exponent_norm mu f +oo else measure_exponent_norm mu f (u^-1)%:E.

(** Source for [measure_positive_reciprocal_exponents]: the set
    U of positive finite norms in Federer 2.4.17, p. 90,
    within the reciprocal exponent domain [0,1]. *)
Definition measure_positive_reciprocal_exponents (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) : set R :=
  [set u | (0 <= u)%R /\ (u <= 1)%R /\ 0 < measure_reciprocal_exponent_norm mu f u /\
    measure_reciprocal_exponent_norm mu f u < +oo].

(** Source for [measure_reciprocal_log_norm]: the logarithmic
    function on U in Federer 2.4.17, p. 90. The finite
    projection is exact on U; values outside U are not specified
    by the convexity assertion. *)
Definition measure_reciprocal_log_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) u :=
  RealExponential.logarithm (fine (measure_reciprocal_exponent_norm mu f u)).

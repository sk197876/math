(** Federer (1969), 2.5.7, p. 98: the total-domain scalar Lebesgue space in
    the linear-functional representation theorem. Erratum p. 2, book p. 98
    line 10, replaces Lp by its total-domain subspace. The underlying
    partial-domain definitions remain those of 2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableRealNormed CountablyMeasurableUP
  MeasureLpMembershipUP MeasureLinfinityUP MeasureExponentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_function]: the total-domain embedding required
    by Federer's erratum p. 2, book p. 98 line 10, for 2.5.7 *)
Definition total_scalar_function (R : realType) (X : Type) (f : X -> R) :
    partial_function X (real_norm_metric_space (scalar_absolute_value_norm R)) :=
  partial_function_total f.

(** Source for [total_scalar_lp_norm]: the existing abstract Lebesgue norm
    restricted to total scalar functions in Federer 2.5.7, p. 98 *)
Definition total_scalar_lp_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p : \bar R) (f : X -> R) :=
  measure_exponent_norm mu (total_scalar_function f) p.

(** Source for [total_scalar_lp]: exact total-domain space in
    Federer 2.5.7, p. 98, after erratum p. 2, line 10.
    The countably measurable nonzero locus from 2.4.12, p. 86,
    is retained also at infinity. Scalar essential separability follows
    from measurability and is recovered in the equivalences below. *)
Definition total_scalar_lp (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p : \bar R) : set (X -> R) :=
  [set f | 1 <= p /\ is_measure_measurable_function mu (total_scalar_function f) /\
    total_scalar_lp_norm mu p f < +oo /\
    is_countably_measure_measurable_function mu
      (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function f)].

(** Source for [total_scalar_lp_finite_equivalence]: compatibility with the
    finite-p definition 2.4.12, p. 86, for the corrected domain of Federer
    2.5.7, p. 98 *)
Lemma total_scalar_lp_finite_equivalence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) (f : X -> R) :
  total_scalar_lp mu p%:E f <->
  @is_measure_lp_function R X R^o (fun y : R => `|y|%R) (scalar_absolute_value_norm R)
    mu p (total_scalar_function f).
Proof.
split.
- move=> [hp [hf [hn hc]]]; split; first by move: hp; rewrite lee_fin.
  split; first exact: (@measurable_real_function_in_normed_space R X mu hm _ hf).
  by split.
- move=> [hp [hf [hn hc]]]; split; first by rewrite lee_fin.
  by split; [exact: hf.1|split].
Qed.

(** Source for [total_scalar_lp_infinity_equivalence]: compatibility with
    the infinity case of 2.4.12, p. 86, for Federer 2.5.7, p. 98 No
    sigma-finiteness of X is inserted. *)
Lemma total_scalar_lp_infinity_equivalence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  total_scalar_lp mu +oo f <->
  @is_measure_linfinity_function R X R^o (fun y : R => `|y|%R) (scalar_absolute_value_norm R)
    mu (total_scalar_function f).
Proof.
split.
- move=> [hp [hf [hn hc]]]; split.
  + exact: (@measurable_real_function_in_normed_space R X mu hm _ hf).
  + by split.
- move=> [hf [hn hc]]; split; first exact: leey.
  by split; [exact: hf.1|split].
Qed.

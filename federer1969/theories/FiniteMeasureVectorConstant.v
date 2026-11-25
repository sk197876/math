(** Supporting constant-vector integral for the first-order error display in
    Federer (1969), 2.9.22, p. 168. The result is a direct consequence of
    the elementary vector integrals of 2.4.12, pp. 87–88; it does not
    construct a new integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionBasic
  MeasureUP MeasureBasic MeasureSplit CharacteristicFunctionUP
  MeasureVectorIntegralUP MeasureVectorCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_measure_vector_constant_integral]:
    supporting integral of v(x) treated as a constant in t,
    Federer 2.9.22, p. 168, norm-error display. For a
    finite measure of total mass m, the constant vector z
    has actual vector integral m z, including m=0 or z=0. *)
Lemma finite_measure_vector_constant_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R) (z : E) :
  mu setT=m%:E -> is_measure_vector_integral mu
    (partial_function_total (fun _ : X => (z : real_norm_metric_space hN))) (m *: z).
Proof.
move=> hmass.
have hs : is_characteristic_function (@setT X) (fun _ : X => (1 : R)).
  constructor; first by [].
  by move=> x hn; exact: False_ind _ (hn I).
have hi := @measure_vector_characteristic_integral R X E N hN mu hm setT
  (fun _ : X => (1 : real_line_metric R)) m z hs (measure_measurable_whole hm) hmass.
have he : (fun _ : X => (1 *: z : real_norm_metric_space hN))=(fun _ : X => z).
  by apply/funext=> x; rewrite scale1r.
by rewrite he in hi.
Qed.

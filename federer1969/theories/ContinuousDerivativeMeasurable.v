(** Federer (1969), 2.9.22, p. 167: the scalar evaluations of the proposed
    derivative field are measurable. This supporting proof writes scalar
    derivatives as almost-everywhere limits of continuous difference
    quotients. It uses only scalar arithmetic continuity from the narrow
    num_normedtype, pseudometric_normed_Zmodule and normed_module
    background, and the project's proved measurable-limit theorem of
    2.3.2(6), pp. 73–74. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP BorelFunctionBasic
  MeasurableFunctionUP MeasurableTotalLimits RealCurveDerivativeUP PuncturedRealSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_map_measure_measurable]: supporting
    continuous-test measurability in Federer 2.9.22, p. 167,
    from the Borel inverse-image facts of 2.3.2, p. 73.
    A total continuous map is measurable for any Borel regular
    measure on its source; no separability is needed here. *)
Lemma continuous_map_measure_measurable (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (f : X -> Y) :
  is_measure mu -> is_borel_regular_measure mu -> continuous f ->
  is_measure_measurable_function mu (partial_function_total f).
Proof.
move=> hm hr hf; constructor.
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
move=> U ho; rewrite partial_function_total_preimage.
exact (@borel_regular_borel_measurable R X mu hm hr _
  (@continuous_borel_function X Y f hf U ho)).
Qed.

(** Source for [continuous_real_difference_quotient]: supporting
    fixed nonzero-increment scalar quotient for Federer 2.9.22,
    p. 167. Continuity in x follows from real addition,
    subtraction and multiplication by the fixed inverse h^-1.
    The assertion also holds for h=0 under the field convention;
    only positive increments are used for derivative limits. *)
Lemma continuous_real_difference_quotient (R : realType) (g : R -> R) (h : R) :
  continuous (g : real_line_metric R -> real_line_metric R) ->
  continuous ((fun x => (g (x+h)-g x)/h) : real_line_metric R -> real_line_metric R).
Proof.
move=> hg.
change (continuous (g : R^o -> R^o)) in hg.
change (continuous ((fun x => (g (x+h)-g x)/h) : R^o -> R^o)).
move=> x; apply: cvgM; last exact: cvg_cst.
apply: cvgB; last exact: hg x.
have hc : (fun t : real_line_metric R => t+h) @ nbhs x --> (x+h : real_line_metric R).
  apply: cvgD; [exact: cvg_id|exact: cvg_cst].
exact: continuous_comp hc (hg (x+h)).
Qed.

(** Source for [continuous_scalar_derivative_representative_measurable]:
    supporting measurable scalar derivatives in Federer 2.9.22,
    p. 167. Any total map agreeing with the actual derivative
    almost everywhere is measurable, by the proved sequence-limit
    theorem of 2.3.2(6). This does not identify a sequence limit
    with a two-sided derivative in the converse direction. *)
Theorem continuous_scalar_derivative_representative_measurable (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (g v : R -> R) :
  is_measure mu -> is_borel_regular_measure mu ->
  continuous (g : real_line_metric R -> real_line_metric R) ->
  measure_almost_everywhere mu [set x | has_real_curve_derivative g x (v x)] ->
  is_measure_measurable_function mu (partial_function_total (v : real_line_metric R -> real_line_metric R)).
Proof.
move=> hm hr hg hd.
pose q (n : nat) (x : real_line_metric R) : real_line_metric R :=
  (g (x+(n.+1%:R : R)^-1)-g x)/(n.+1%:R : R)^-1.
have hq n : is_measure_measurable_function mu (partial_function_total (q n)).
  apply: (continuous_map_measure_measurable hm hr).
  exact: continuous_real_difference_quotient hg.
apply: (@measurable_total_functions_almost_limit R (real_line_metric R)
  [the metricType R of real_line_metric R] mu hm q v
  [set x | has_real_curve_derivative g x (v x)] hq hd)=> x hx.
exact: punctured_real_limit_reciprocal_sequence hx.
Qed.

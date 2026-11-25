(** Federer (1969), proof of 2.4.4(2), p. 83: the geometric step approximant
    of a nonnegative measurable function finite almost everywhere. The
    scalar cell selection is supplied through its laws; replacing infinite
    input values by zero is used only to define the approximant off the
    conull finite-value region. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic TopologicalBorel
  ExtendedFiniteProjectionBorel GeometricQuantisationUP GeometricQuantisationBorel
  MeasureStepFunctionUP MeasureStepNonnegative NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_geometric_approximant]: the geometric
    step approximant u in Federer 2.4.4(2), p. 83.
    It retains the source partial domain; infinite values are
    projected to zero, and their nullity is checked when comparing
    u with f. Federer assigns zero on all of X outside the
    positive-value locus; here the approximant is left undefined
    outside f's original conull domain. This difference affects
    only a null set and leaves both approximant inequalities intact. *)
Definition partial_geometric_approximant (R : realType) (X : Type) (q : R -> R)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun z => (q (fine z) : real_line_metric R)).

(** Source for [geometric_quantisation_nonnegative]: supporting
    nonnegativity of all values of the geometric approximant in
    Federer 2.4.4(2), p. 83. *)
Lemma geometric_quantisation_nonnegative (R : realType) (t : R) (q : R -> R) :
  (1 < t)%R -> is_geometric_quantisation t q -> forall x, (0 <= q x)%R.
Proof.
move=> ht hq x; have [hx|hx] := leP x 0%R.
- by rewrite (hq.1 x hx).
- have [j [_ [_ he]]] := hq.2 x hx; rewrite he.
  apply: exprz_ge0; exact: le_trans ler01 (ltW ht).
Qed.

(** Source for [measurable_geometric_approximant]: measurability
    of u in Federer 2.4.4(2), p. 83, by the
    Borel scalar cell map and the measurable-function composition law. *)
Lemma measurable_geometric_approximant (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : R) (q : R -> R)
    (f : partial_function X (extended_real_line R)) :
  (1 < t)%R -> is_geometric_quantisation t q -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_geometric_approximant q f).
Proof.
move=> ht hq hf; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm f _ hf).
move=> U hU; change (borel_set ((fun z : extended_real_line R => (fine z : real_line_metric R)) @^-1`
  ((fun x : real_line_metric R => (q x : real_line_metric R)) @^-1` U))).
apply: (@borel_function_preimage _ _ _ (@extended_finite_projection_borel R)).
exact: (@geometric_quantisation_borel R t q ht hq U hU).
Qed.

(** Source for [geometric_approximant_countable_range]: countable
    range of u in Federer 2.4.4(2), p. 83; its
    values lie among zero and the integer powers of t. *)
Lemma geometric_approximant_countable_range (R : realType) (X : Type)
    (t : R) (q : R -> R) (f : partial_function X (extended_real_line R)) :
  is_geometric_quantisation t q -> countable (partial_function_range (partial_geometric_approximant q f)).
Proof.
move=> hq; apply: sub_countable _ (geometric_quantisation_range_countable hq).
apply: subset_card_le=> y [x [z [hz he]]]; exists (fine z)=> //.
Qed.

(** Source for [geometric_approximant_step]: u is a step
    function in the sense of Federer 2.4.1, as required
    in the proof of 2.4.4(2), p. 83. Its
    nonnegative assigned sum is allowed to be infinite. *)
Lemma geometric_approximant_step (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : R) (q : R -> R)
    (f : partial_function X (extended_real_line R)) :
  (1 < t)%R -> is_geometric_quantisation t q -> is_measure_measurable_function mu f ->
  is_measure_step_function mu (partial_geometric_approximant q f).
Proof.
move=> ht hq hf; have hum := @measurable_geometric_approximant R X mu hm t q f ht hq hf.
have hp : measure_almost_everywhere mu (partial_real_nonnegative_locus (partial_geometric_approximant q f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hum)).
  move=> x [y [z [hz he]]]; exists y; split; first by exists z.
  rewrite -he; exact (@geometric_quantisation_nonnegative R t q ht hq (fine z)).
have hcoef y : (@setT R) y -> 0 <= y%:E*mu (partial_function_preimage (partial_geometric_approximant q f) [set y]).
  move=> _; exact (@measure_step_nonnegative_coefficients R X mu hm _ hp y).
constructor=> //.
- exact (@geometric_approximant_countable_range R X t q f hq).
- eexists; rewrite /is_measure_step_integral; exact: numerical_sum_nonnegative hcoef.
Qed.

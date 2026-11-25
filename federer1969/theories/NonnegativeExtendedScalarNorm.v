(** Federer (1969), 2.10.5, p. 172, bounded- set paragraph: after proving
    that f_S is finite, apply the scalar exponent results of 2.4.17, p. 90.
    Prove agreement of the extended-input norm with the existing scalar norm
    first. Measurability of the finite-part map alone does not justify
    replacing infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormPowerScalar
  ScalarNormExtendedEmbedding ExtendedRealOrderTopology ExtendedFiniteProjectionBorel
  PartialFunctionUP PartialFunctionBasic PartialNormPower MeasureUP MeasureGauge
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  MeasureLpNormUP MeasureLpNorm MeasureEssentialNormUP MeasureEssentialNorm MeasureExponentDomain
  MeasureIntegralGraphEquivalence ExtendedPositivePower RealPower
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_norm_scalar_embedding]:
    supporting agreement of the two L^t interfaces
    for finite nonnegative inputs in Federer
    2.10.5, p. 172. Integral and essential-
    bound uniqueness prove equality at every t>=1. *)
Theorem nonnegative_extended_norm_scalar_embedding (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (t : \bar R) :
  (forall x, (0<=g x)%R) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total g) ->
  nonnegative_extended_exponent_norm mu (fun x => (g x)%:E) t =
    measure_exponent_norm mu (partial_function_total g) t.
Proof.
move=> hg0 ht hg.
have hge : @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x => (g x)%:E)).
  apply: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hm g (fun y => y%:E) hg).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hnew := @nonnegative_extended_exponent_norm_specification R X mu
  (fun x => (g x)%:E) t hm (fun x => hg0 x) ht hge.
apply: (@nonnegative_extended_exponent_norm_unique R X mu (fun x => (g x)%:E) t _ _ hnew).
clear hnew.
case: t ht=> [p| |] ht //=.
- have hp : (1<=p)%R := ht.
  have [_ [b [hbi he]]] := @measure_lp_norm_specification R X R^o
    (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu p (partial_function_total g) hm hp hg.
  split=> //; exists b; split=> //.
  apply: (measure_integral_graph_equivalent _ hbi)=> x z; split.
  - move=> [y [hy hyz]].
    have hy' : g x=y := hy.
    have hz' : (real_power `|y|%R p)%:E=z := hyz.
    change ((real_power (g x) p)%:E=z).
    by rewrite -hy' (ger0_norm (hg0 x)) in hz'.
  - move=> hz; exists (g x); split=> //.
    change ((real_power `|g x|%R p)%:E=z).
    by rewrite (ger0_norm (hg0 x)).
- have hsup r : [set x | r<(g x)%:E] =
      partial_norm_superlevel (fun y : R => `|y|%R) (partial_function_total g) r.
    apply/seteqP; split=> x.
    - move=> hx; exists (g x); split=> //.
      change (is_true (r<`|g x|%R%:E)).
      by rewrite (ger0_norm (hg0 x)).
    - move=> [y [hy hr]]; have hy' : g x=y := hy.
      have hr' : r<`|y|%R%:E := hr.
      by rewrite -hy' (ger0_norm (hg0 x)) in hr'.
  have [ha hl] := measure_essential_norm_specification mu
    (fun y : R => `|y|%R) (partial_function_total g).
  split.
  - move=> r [hr hz]; apply: ha; split=> //; by rewrite -hsup.
  - move=> b hb; apply: hl=> r [hr hz]; apply: hb; split=> //; by rewrite hsup.
Qed.

(** Source for [measurable_extended_finite_scalar]:
    supporting measurable scalar representative for
    Federer 2.10.5, p. 172. This lemma
    asserts only measurability; the next comparison
    separately requires every original value finite. *)
Lemma measurable_extended_finite_scalar (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total
    (fun x => (fine (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hf.
have hreal := @measurable_total_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm f
  (fun y => (fine y : real_line_metric R)) hf (@extended_finite_projection_borel R).
apply: (@measurable_total_borel_postcomposition R X
  [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  mu hm (fun x => (fine (f x) : real_line_metric R)) (fun y => y) hreal).
apply: continuous_borel_function; exact: real_scalar_norm_identity_continuous.
Qed.

(** Source for [nonnegative_extended_norm_finite_scalar]:
    supporting exact scalar replacement of a finite
    f_S before applying 2.4.17 in Federer 2.10.5,
    p. 172. The explicit finiteness hypothesis
    prevents discarding any infinite projected volumes. *)
Theorem nonnegative_extended_norm_finite_scalar (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> (forall x, f x \is a fin_num) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu f t =
    measure_exponent_norm mu (partial_function_total
      (fun x => (fine (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))) t.
Proof.
move=> hf0 hfin ht hf.
have he : f=(fun x => (fine (f x))%:E) by apply: funext=> x; exact: esym (fineK (hfin x)).
have hg0 x : (0<=fine (f x))%R.
  have h := hf0 x; by rewrite -(fineK (hfin x)) lee_fin in h.
have hg := measurable_extended_finite_scalar hm hf.
rewrite {1}he.
exact: (@nonnegative_extended_norm_scalar_embedding R X mu hm
  (fun x => (fine (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))
  t hg0 ht hg).
Qed.

(** Federer (1969), 2.5.7, p. 98: the measurable functions underlying the
    total-domain Lp lattice. Measurable closure is 2.3.2, pp. 73–74. These
    adapters identify the real-line and scalar norm topologies through
    proved continuous maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ScalarNormExtendedEmbedding NormPowerScalar
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasurableRealPairs MeasurablePostcomposition MeasurableGraphEquivalence MeasurableTotalBasic BorelFunctionBasic
  FunctionLatticeUP VectorFunctionLattice TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_scalar_real_measurable]: supporting real-line topology
    identification for Federer 2.5.7, p. 98 *)
Lemma total_scalar_real_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (partial_function_total (f : X -> real_line_metric R)).
Proof.
move=> hf; exact: (@measurable_total_borel_postcomposition R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  [the topologicalType of real_line_metric R] mu hm f (fun y => y) hf
  (continuous_borel_function (@ScalarNormExtendedEmbedding.scalar_norm_real_identity_continuous R))).
Qed.

(** Source for [real_total_scalar_measurable]: reverse topology
    identification supporting Federer 2.5.7, p. 98 *)
Lemma real_total_scalar_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_measure_measurable_function mu (partial_function_total (f : X -> real_line_metric R)) ->
  is_measure_measurable_function mu (total_scalar_function f).
Proof.
move=> hf; exact: (@measurable_total_borel_postcomposition R X
  [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm f (fun y => y) hf
  (continuous_borel_function (@real_scalar_norm_identity_continuous R))).
Qed.

(** Source for [total_scalar_continuous_operation]: supporting unary closure
    of the Lp lattice in Federer 2.5.7, p. 98, by measurable composition
    2.3.2(4), p. 73 *)
Lemma total_scalar_continuous_operation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R)
    (a : real_line_metric R -> real_line_metric R) :
  continuous a -> is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function (fun x => a (f x))).
Proof.
move=> ha hf; apply: (@real_total_scalar_measurable R X mu hm).
exact: (@measurable_total_borel_postcomposition R X
  [the topologicalType of real_line_metric R] [the topologicalType of real_line_metric R]
  mu hm f a (total_scalar_real_measurable hm hf) (continuous_borel_function ha)).
Qed.

(** Source for [total_scalar_continuous_binary_operation]: supporting binary
    closure used in Federer 2.5.7, p. 98; measurable real arithmetic and
    extrema come from 2.3.2, pp. 73–74 *)
Lemma total_scalar_continuous_binary_operation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R)
    (a : (real_line_metric R * real_line_metric R)%type -> real_line_metric R) :
  continuous a -> is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  is_measure_measurable_function mu (total_scalar_function (fun x => a (f x,g x))).
Proof.
move=> ha hf hg; apply: (@real_total_scalar_measurable R X mu hm).
have hp := @measurable_real_function_pair R X mu hm
  (partial_function_total (f : X -> real_line_metric R))
  (partial_function_total (g : X -> real_line_metric R))
  (total_scalar_real_measurable hm hf) (total_scalar_real_measurable hm hg).
have hb := @measurable_function_borel_postcomposition R X
  [the topologicalType of (real_line_metric R * real_line_metric R)%type]
  [the topologicalType of real_line_metric R] mu hm _ a hp (continuous_borel_function ha).
apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R] mu _ _ _ hb)=> x z; split.
- move=> [[u v] [[hu hv] he]].
  have hu' : f x=u := hu.
  have hv' : g x=v := hv.
  change (a (f x,g x)=z); by rewrite hu' hv'.
- move=> he; exists (f x,g x); by split; [split|].
Qed.

(** Source for [total_scalar_measurable_lattice]: the full measurable
    lattice underlying Federer 2.5.7, p. 98, from 2.3.2, pp. 73–74, and
    2.5.1, p. 91 *)
Theorem total_scalar_measurable_lattice (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_function_lattice [set f : X -> R | is_measure_measurable_function mu (total_scalar_function f)].
Proof.
constructor.
- move=> f g hf hg; apply: (@total_scalar_continuous_binary_operation R X mu hm f g (fun p => p.1+p.2) _ hf hg).
  change (continuous (fun p : R^o * R^o => p.1+p.2)); exact: add_continuous.
- move=> c f hc hf; apply: (@total_scalar_continuous_operation R X mu hm f (fun y => c*y) _ hf).
  change (continuous (fun y : R^o => c*y)).
  move=> y; apply: cvgM; [exact: cvg_cst|exact: cvg_id].
- move=> f g hf hg; apply: (@total_scalar_continuous_binary_operation R X mu hm f g (fun p => Order.min p.1 p.2) _ hf hg).
  change (continuous (fun p : R^o * R^o => Order.min p.1 p.2)).
  move=> p; apply: continuous_min; [exact: cvg_fst|exact: cvg_snd].
- move=> c f hc hf; apply: (@total_scalar_continuous_operation R X mu hm f (fun y => Order.min y c) _ hf).
  change (continuous (fun y : R^o => Order.min y c)).
  move=> y; apply: continuous_min; [exact: cvg_id|exact: cvg_cst].
- move=> f g hf hg hfg; apply: (@total_scalar_continuous_binary_operation R X mu hm g f (fun p => p.1-p.2) _ hg hf).
  change (continuous (fun p : R^o * R^o => p.1-p.2)).
  move=> p; apply: cvgB; [exact: cvg_fst|exact: cvg_snd].
Qed.

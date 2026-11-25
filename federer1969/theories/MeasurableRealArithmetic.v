(** Federer (1969), 2.3.2, p. 74: closure under ordinary real addition,
    subtraction, and multiplication. The narrow pseudometric_normed_Zmodule
    and normed_module imports supply only scalar arithmetic continuity, as
    in BaireRealAlgebra. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal
  topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPair
  PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP MeasurableRealPairs
  MeasurablePostcomposition BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [partial_real_function_add]: direct ordinary real sum of
    Federer 2.3.2, p. 74, defined on the intersection of the input domains *)
Definition partial_real_function_add (R : realType) (X : Type)
    (f g : partial_function X (real_line_metric R)) :=
  partial_function_postcompose (partial_function_pair f g)
    (fun p => (p.1 + p.2 : real_line_metric R)).

(** Source for [partial_real_function_subtract]: direct ordinary real
    difference in Federer 2.3.2, p. 74, on the common domain. *)
Definition partial_real_function_subtract (R : realType) (X : Type)
    (f g : partial_function X (real_line_metric R)) :=
  partial_function_postcompose (partial_function_pair f g)
    (fun p => (p.1 - p.2 : real_line_metric R)).

(** Source for [partial_real_function_multiply]: direct ordinary real
    product in Federer 2.3.2, p. 74, on the common domain. *)
Definition partial_real_function_multiply (R : realType) (X : Type)
    (f g : partial_function X (real_line_metric R)) :=
  partial_function_postcompose (partial_function_pair f g)
    (fun p => (p.1 * p.2 : real_line_metric R)).

(** Source for [measurable_real_function_add]: direct ordinary real additive
    closure in Federer 2.3.2, p. 74 *)
Theorem measurable_real_function_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_real_function_add f g).
Proof.
move=> hf hg; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm).
- exact (@measurable_real_function_pair R X mu hm f g hf hg).
- apply: continuous_borel_function.
  change (continuous (fun p : R^o * R^o => p.1 + p.2)); exact: add_continuous.
Qed.

(** Source for [measurable_real_function_subtract]: direct ordinary real
    subtraction closure in Federer 2.3.2, p. 74 *)
Theorem measurable_real_function_subtract (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_real_function_subtract f g).
Proof.
move=> hf hg; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm).
- exact (@measurable_real_function_pair R X mu hm f g hf hg).
- apply: continuous_borel_function.
  change (continuous (fun p : R^o * R^o => p.1 - p.2)).
  move=> p; apply: cvgB; [exact: cvg_fst|exact: cvg_snd].
Qed.

(** Source for [measurable_real_function_multiply]: direct ordinary real
    multiplicative closure in Federer 2.3.2, p. 74 No additional domain
    hypothesis is needed because the two input domains are conull. *)
Theorem measurable_real_function_multiply (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_real_function_multiply f g).
Proof.
move=> hf hg; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm).
- exact (@measurable_real_function_pair R X mu hm f g hf hg).
- apply: continuous_borel_function.
  change (continuous (fun p : R^o * R^o => p.1 * p.2)).
  move=> p; apply: cvgM; [exact: cvg_fst|exact: cvg_snd].
Qed.

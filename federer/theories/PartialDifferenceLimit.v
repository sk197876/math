(** Federer (1969), 2.4.12, p. 87: the infinity-endpoint completeness
    argument through convergence in measure and an almost-everywhere
    convergent subsequence. These statements retain partial domains and
    allow infinite individual norms; membership in the finite-norm Lebesgue
    space is a separate condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricSubtractContinuity PartialFunctionUP
  PartialFunctionLimitUP PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_difference_almost_limit]: supporting
    convergence of f_n-g_m to f_n-h in Federer 2.4.12,
    p. 87, with the first function fixed. The limit locus
    records all defined values and keeps their common domain. *)
Lemma partial_difference_almost_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (a : partial_function X (real_norm_metric_space hN))
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  measure_almost_everywhere mu (partial_function_domain a) ->
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => partial_vector_subtract a (f n)) (partial_vector_subtract a g)).
Proof.
move=> ha hl.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ ha hl)).
move=> x [[y hy] [u [z [hu [hz hlim]]]]].
exists (fun n => (y-u n)%R), (y-z)%R; split.
- move=> n; apply/partial_vector_subtract_graph; exists y,(u n); by split=> //; split.
- split.
  + apply/partial_vector_subtract_graph; exists y,z; by split=> //; split.
  + have hp : (fun n => (y,u n)) @ \oo --> (y,z) := cvg_pair (cvg_cst y) hlim.
    move=> W hW; exact: hp _ (@real_norm_metric_subtract_continuous R V N hN (y,z) W hW).
Qed.

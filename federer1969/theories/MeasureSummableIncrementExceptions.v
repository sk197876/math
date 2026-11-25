(** Federer (1969), 2.3.9, p. 79: the sets X-A_n consist of points where the
    successive difference exceeds its gauge. The common undefined locus is
    explicitly included; it is null because every input lies in A(mu,Y).
    Source context: PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP
  PartialNormedArithmetic MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableFunctionBasic MeasurableNormedFunctionUP
  MeasurableNormedDifference MeasurableNormSuperlevels MeasureGauge MeasureGaugeAttainment
  MeasureConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_sequence_common_domain]: supporting
    explicit common domain for the sequence in Federer 2.3.9,
    p. 79, consistent with 2.3.2(6), pp. 73–74. *)
Definition partial_sequence_common_domain (X Y : Type) (f : nat -> partial_function X Y) :=
  \bigcap_n partial_function_domain (f n).

(** Source for [measure_increment_exception]: complement of A_n
    in Federer 2.3.9, p. 79, enlarged by the null
    common undefined locus to make all sequence values available. *)
Definition measure_increment_exception (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f : nat -> partial_function X V) n :=
  (~` partial_sequence_common_domain f) `|`
  partial_norm_superlevel N (partial_vector_subtract (f n.+1) (f n))
    (measure_normed_distance mu N (f n.+1) (f n)).

(** Source for [measurable_sequence_common_domain_conull]:
    supporting removal of the common undefined locus in Federer
    2.3.9, p. 79; no total-domain assumption is added. *)
Lemma measurable_sequence_common_domain_conull (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X Y) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  measure_almost_everywhere mu (partial_sequence_common_domain f).
Proof.
move=> hf; apply: (@measure_almost_everywhere_countable R X nat mu hm setT
  (fun n => partial_function_domain (f n)) (countableP _))=> n _.
exact: measurable_function_domain (hf n).
Qed.

(** Source for [measure_increment_exception_bound]: direct
    attainment estimate mu(X-A_n) <= |g_(n+1)-g_n|_mu in
    Federer 2.3.9, p. 79, with the null domain correction. *)
Lemma measure_increment_exception_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) -> forall n,
  mu (measure_increment_exception mu N f n) <= measure_normed_distance mu N (f n.+1) (f n).
Proof.
move=> hf n.
have hd := @measurable_sequence_common_domain_conull R X
  [the topologicalType of real_norm_metric_space hN] mu hm f (fun n => (hf n).1).
have hh := @measure_binary_cover R X mu hm (measure_increment_exception mu N f n)
  (~` partial_sequence_common_domain f)
  (partial_norm_superlevel N (partial_vector_subtract (f n.+1) (f n))
    (measure_normed_distance mu N (f n.+1) (f n))) (fun x hx => hx).
rewrite hd add0e in hh; apply: le_trans hh _.
have hdiff := @measurable_normed_function_subtract R X V N hN mu hm (f n.+1) (f n) (hf n.+1) (hf n).
exact: (@measurable_norm_gauge_attained R X V N hN mu hm _ hdiff.1).2.
Qed.

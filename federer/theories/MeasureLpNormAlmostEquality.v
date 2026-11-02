(** Federer (1969), 2.4.12, pp. 86–87, and 2.4.15, p. 89: norm values depend
    on the almost-everywhere norms of the functions. These supporting
    substitution laws follow from the integral-root specification; infinite
    norm values and exact partial domains are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureLpNorm
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_equality_locus]: supporting
    common-domain norm equality in the condition of Federer
    2.4.15, p. 89. Both original values must
    exist; exceptional undefined values are not filled in. *)
Definition partial_norm_equality_locus (R : realType) (X Y : Type)
    (N : Y -> R) (f g : partial_function X Y) :=
  [set x | exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ N a=N b].

(** Source for [measure_lp_norm_almost_norm_equal]: supporting
    integral substitution for the equality criterion in Federer
    2.4.15, p. 89, using the norm formula
    of 2.4.12, p. 86. Infinite norm values
    are permitted; no summability hypothesis is added. *)
Lemma measure_lp_norm_almost_norm_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_norm_equality_locus N f g) ->
  measure_lp_norm mu N p f = measure_lp_norm mu N p g.
Proof.
move=> hp hf hg he.
have [_ [a [hai hfa]]] := @measure_lp_norm_specification R X V N hN mu p f hm hp hf.
have [_ [b [hbi hgb]]] := @measure_lp_norm_specification R X V N hN mu p g hm hp hg.
have hepow : measure_almost_equal mu (partial_norm_power N p f) (partial_norm_power N p g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [u [v [hu [hv huv]]]]; exists (real_power (N u) p)%:E; split.
  - exists u; by split.
  - exists v; split=> //; by rewrite huv.
have hgi := @measure_integral_almost_equal R X mu hm _ _ a hai hepow.
have hab := @measure_integral_unique R X mu _ a b hgi hbi.
by rewrite hfa hgb hab.
Qed.

(** Source for [measure_lp_norm_almost_equal]: null-modification
    invariance of the finite-p norm in Federer 2.4.12,
    pp. 86–87, supporting the equality and completeness
    arguments. The partial domains may differ on null sets. *)
Lemma measure_lp_norm_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_equal mu f g -> measure_lp_norm mu N p f = measure_lp_norm mu N p g.
Proof.
move=> hp hf hg he; apply: (@measure_lp_norm_almost_norm_equal R X V N hN mu hm p f g hp hf hg).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [hu hgu]]; exists u,u; by split=> //; split.
Qed.

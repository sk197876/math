(** Federer (1969), 2.5.7, p. 98: the increasing limit of a sequence in U is
    almost equal to a member of U. These supporting adapters compose the
    sealed lower limit with the Borel finite projection; no replacement is
    claimed almost equal without a finiteness proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic ScalarNormExtendedEmbedding
  ExtendedFiniteProjectionBorel ExtendedLowerLimit ExtendedRealOrderLimit
  TotalExtendedLowerLimit TotalScalarLpUP TotalScalarMeasurability TotalScalarSupport
  CountablyMeasurableUP CountablyMeasurableUnions CountablyMeasurableSubsets IncreasingScalarErrors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_lower_limit_replacement]: supporting real
    representative of the candidate limit in Federer 2.5.7, p. 98 Either
    infinite value is replaced by zero, through the already proved Borel
    map. *)
Definition real_lower_limit_replacement (R : realType) (X : Type)
    (f : nat -> X -> R) (x : X) : R :=
  fine (total_extended_lower_limit (fun n x => (f n x)%:E) x).

(** Source for [real_lower_limit_replacement_measurable]: measurable
    replacement used in Federer 2.5.7, p. 98 *)
Lemma real_lower_limit_replacement_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : nat -> X -> R) :
  (forall n, is_measure_measurable_function mu (total_scalar_function (f n))) ->
  is_measure_measurable_function mu (total_scalar_function (real_lower_limit_replacement f)).
Proof.
move=> hf; apply: (@real_total_scalar_measurable R X mu hm).
apply: (@measurable_total_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm _ (fun y => fine y)).
- apply: (@total_extended_lower_limit_measurable R X mu hm)=> n.
  exact: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hm (f n) (fun y => y%:E) (hf n)
    (continuous_borel_function (@scalar_norm_extended_embedding_continuous R))).
- exact: extended_finite_projection_borel.
Qed.

(** Source for [real_lower_limit_replacement_nonnegative]: positivity of the
    representative in Federer 2.5.7, p. 98 Zero replacement retains
    positivity even on the exceptional infinite-value set. *)
Lemma real_lower_limit_replacement_nonnegative (R : realType) (X : Type)
    (f : nat -> X -> R) :
  (forall n x, (0 <= f n x)%R) -> forall x, (0 <= real_lower_limit_replacement f x)%R.
Proof.
move=> hf x; apply: fine_ge0; apply: total_extended_lower_limit_nonnegative.
by move=> n y; rewrite lee_fin; exact: hf.
Qed.

(** Source for [real_lower_limit_replacement_zero]: the support inclusion
    used in Federer 2.5.7, p. 98 *)
Lemma real_lower_limit_replacement_zero (R : realType) (X : Type)
    (f : nat -> X -> R) (x : X) :
  (forall n, f n x=0%R) -> real_lower_limit_replacement f x=0%R.
Proof.
move=> hz; rewrite /real_lower_limit_replacement /total_extended_lower_limit.
have he : (fun n => (f n x)%:E)=(fun _ : nat => (0%R)%:E).
  by apply: funext=> n; rewrite hz.
by rewrite he extended_lower_limit_constant.
Qed.

(** Source for [real_lower_limit_replacement_countable_support]: countably
    measurable support of the limit in Federer 2.5.7, p. 98 No countable
    measurability of the entire ambient space is inserted here. *)
Lemma real_lower_limit_replacement_countable_support (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : nat -> X -> R) :
  (forall n, is_countably_measure_measurable_function mu
    (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function (f n))) ->
  is_countably_measure_measurable_function mu
    (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (total_scalar_function (real_lower_limit_replacement f)).
Proof.
move=> hf.
have hg := @real_lower_limit_replacement_measurable R X mu hm f
  (fun n => countably_measurable_function_measurable (hf n)).
constructor=> //.
have hC := @countably_measurable_countable_union R X [the choiceType of (nat : Type)] mu setT
  (fun n => partial_function_nonzero_locus 0%R (total_scalar_function (f n)))
  (countableP setT) (fun n => countably_measurable_function_locus (hf n)).
apply: (@measurable_subset_countably_measurable R X mu hm _ _
  (@total_scalar_nonzero_locus_measurable R X mu hm _ hg) _ hC).
move=> x [y [hy hy0]].
have hex : exists n, f n x <> 0%R.
  apply: contrapT=> hn.
  apply: hy0; have he : real_lower_limit_replacement f x=y := hy.
  rewrite -he; apply: real_lower_limit_replacement_zero=> n.
  case: (eqVneq (f n x) 0%R)=> // hne.
  exfalso; apply: hn; exists n; exact/eqP.
have [n hn] := hex; exists n=> //; exists (f n x); by split.
Qed.

(** Source for [real_lower_limit_replacement_converges]: the
    almost-everywhere convergence to the finite representative in Federer
    2.5.7, p. 98 Finiteness is an explicit premise, subsequently proved from
    the uniform Lq bound. *)
Lemma real_lower_limit_replacement_converges (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : nat -> X -> R) :
  (forall n m x, (n <= m)%N -> (f n x <= f m x)%R) ->
  measure_almost_everywhere mu
    [set x | total_extended_lower_limit (fun n x => (f n x)%:E) x \is a fin_num] ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => total_scalar_function (f n)) (total_scalar_function (real_lower_limit_replacement f))).
Proof.
move=> hinc hfin; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfin)=> x hx.
exists (fun n => (f n x : real_norm_metric_space (scalar_absolute_value_norm R))),
  (real_lower_limit_replacement f x : real_norm_metric_space (scalar_absolute_value_norm R)).
split=> //; split=> //; apply: real_order_limit_scalar_norm_sequence.
rewrite /real_lower_limit_replacement (fineK hx).
have hi : forall n m y, (n <= m)%N -> (f n y)%:E <= (f m y)%:E.
  by move=> n m y hnm; rewrite lee_fin; exact: hinc.
exact: (@total_extended_lower_limit_increases R X _ hi x).2.
Qed.

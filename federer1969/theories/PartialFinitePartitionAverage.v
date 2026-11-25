(** Federer (1969), 2.3.8, p. 79: the finite average representation on each
    function's original domain. This version retains the partial functions
    of the corrected set A(mu,Y), rather than asserting a literal
    vector-space structure; erratum p. 1, book p. 78 line 7. Source
    editions: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionSourceRestriction MeasurableFunctionUP
  MeasureUP MeasurableNormedFunctionUP MeasurableNormedBasic MeasurableNormedRestriction
  MeasurableTotalNormedArithmetic CharacteristicFunctionUP CharacteristicFunctionSealed
  CharacteristicVectorPiece MeasureGauge FinitePartitionAverage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_finite_partition_average]: direct pointwise
    version of Federer's finite-average identity, 2.3.8,
    p. 79, preserving the original domain of every summand.
    Each summand belongs to A(mu,Y) and has gauge at most e.
    The equal weights are nonnegative and sum to one by
    [finite_average_nonnegative_weights] and [finite_average_weights_sum]. *)
Theorem partial_finite_partition_average (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (e : R)
    n (S : 'I_n -> set X) (f : partial_function X (real_norm_metric_space hN)) :
  (0 < n)%N -> (forall i, measure_measurable mu (S i)) ->
  (forall i, mu (S i) <= e%:E) ->
  (forall x, exists i, S i x) -> (forall i j x, S i x -> S j x -> i=j) ->
  is_measurable_normed_function mu f ->
  exists u : 'I_n -> partial_function X (real_norm_metric_space hN),
    (forall i, is_measurable_normed_function mu (u i) /\
      measure_gauge mu N (u i) <= e%:E /\
      partial_function_domain (u i) = partial_function_domain f) /\
    forall x y, partial_function_graph f x y ->
      exists v : 'I_n -> V, (forall i, partial_function_graph (u i) x (v i)) /\
        y = (\sum_(i < n) n%:R^-1 *: v i)%R.
Proof.
move=> hn hS hb hc hd hf.
have [g [hg [ha hmg]]] := @measurable_normed_total_representative R X V N hN mu hm f hf.
pose s i := @CharacteristicFunction.value R X (S i).
have hs i := @CharacteristicFunction.laws R X (S i).
pose v i := characteristic_vector_piece (s i) (fun x => (n%:R *: g x)%R).
pose u i := partial_function_source_restrict (partial_function_domain f) (partial_function_total (v i)).
have hmv i : is_measurable_normed_function mu (partial_function_total (v i)).
  apply: (@measurable_normed_characteristic_piece R X V N hN mu hm (S i) (s i)
    (fun x => (n%:R *: g x)%R) (hs i) (hS i)).
  exact (@measurable_normed_total_scale R X V N hN mu hm n%:R g hmg).
exists u; split.
- move=> i.
  have [hmu he] := @measurable_normed_conull_restriction R X V N hN mu hm
    (partial_function_domain f) _ (measurable_function_domain hf.1) (hmv i).
  split; first exact hmu.
  split.
  + rewrite /u he; apply: le_trans (@measure_gauge_characteristic_piece_bound R X V N hN.1
      mu hm (S i) (s i) (fun x => (n%:R *: g x)%R) (hs i)) _.
    exact: hb.
  + by rewrite /u partial_function_source_restrict_domain partial_function_total_domain setIT.
- move=> x y hxy; exists (fun i => v i x); split.
  + move=> i; split=> //; by exists y.
  + rewrite -(hg x y hxy).
    exact (@finite_partition_average_pointwise R X V n S s g hn hs hc hd x).
Qed.

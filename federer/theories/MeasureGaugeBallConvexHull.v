(** Federer (1969), 2.3.8, p. 79: if a finite measurable partition has all
    pieces of measure at most e, the convex hull of B(0,e) fills the
    function space. Source context and explicit total-domain interpretation:
    MeasureGaugeBall.v. The proof uses Federer's displayed equal-weight
    average and the project's Chapter 1 convex-hull universal property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP
  CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicVectorPiece
  MeasurableNormedFunctionUP MeasurableTotalNormedArithmetic TotalMeasurableFunctionSpace
  MeasureGaugeBall MeasureGauge FinitePartitionAverage InnerConvex ConvexHullUP ConvexFiniteCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_partition_measure_ball_convex_hull]: direct
    convex-hull assertion in Federer 2.3.8, p. 79, on total-domain members
    The proof also permits e=0. There are positively many partition pieces,
    as required by the equal-weight formula. *)
Theorem finite_partition_measure_ball_convex_hull (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (e : R)
    n (S : 'I_n -> set X) :
  (0 < n)%N -> (0 <= e)%R ->
  (forall i, measure_measurable mu (S i)) ->
  (forall i, mu (S i) <= e%:E) ->
  (forall x, exists i, S i x) -> (forall i j x, S i x -> S j x -> i=j) ->
  is_convex_hull (@total_measure_gauge_ball R X V N hN mu e) (@total_measurable_normed_set R X V N hN mu).
Proof.
move=> hn he hS hbound hcover hdis; constructor.
- by move=> f [hf _].
- exact: total_measurable_normed_convex hm.
- move=> C hBC hC f hf.
  pose F := GRing.Lmodule.clone R (X -> real_norm_metric_space hN) _.
  pose s i := @CharacteristicFunction.value R X (S i).
  have hs i := @CharacteristicFunction.laws R X (S i).
  pose u i : F := characteristic_vector_piece (s i) (fun x => (n%:R *: f x)%R).
  have hu i : C (u i).
    apply: hBC; split.
    + apply: (@measurable_normed_characteristic_piece R X V N hN mu hm (S i) (s i)
        (fun x => (n%:R *: f x)%R) (hs i) (hS i)).
      exact (@measurable_normed_total_scale R X V N hN mu hm n%:R f hf).
    + apply: le_trans (@measure_gauge_characteristic_piece_bound R X V N hN.1 mu hm
        (S i) (s i) (fun x => (n%:R *: f x)%R) (hs i)) _.
      exact: hbound.
  have h0 : C 0%R := hBC _ (@total_measure_gauge_ball_zero R X V N hN mu hm e he).
  have hw : (\sum_(i < n) (n%:R : R)^-1 <= 1)%R.
    by rewrite (@finite_average_weights_sum R n hn).
  have hsum := @convex_subconvex_sum R F C hC h0 n u (fun _ => ((n%:R : R)^-1)%R)
    hu (fun _ => @finite_average_nonnegative_weights R n) hw.
  have heq := @finite_partition_average_function R X [the lmodType R of real_norm_metric_space hN]
    n S s f hn hs hcover hdis.
  by rewrite -heq in hsum.
Qed.

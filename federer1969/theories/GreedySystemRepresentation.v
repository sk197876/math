(** Federer (1969), 2.3.3, p. 76: consequences of the abstract greedy-system
    laws. No witness implementation is imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic ExtendedRealOrderTopology MeasureUP MeasurableFunctionUP
  WeightedCharacteristicExpansionUP GreedyCharacteristicSystemUP GreedySystemPartialSums
  GreedyScalarExpansionUP GreedyScalarSeries GreedyMeasurableSets NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_system_weighted_representation]: direct conclusion of
    Federer 2.3.3, p. 76, for any system satisfying its greedy formula. The
    equality is at every point, including infinite target values. *)
Theorem greedy_system_weighted_representation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> extended_real_line R)
    (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall x, 0 <= f x) -> is_positive_vanishing_divergent_sequence r ->
  is_greedy_characteristic_system f r A g -> is_weighted_characteristic_expansion mu f r A g.
Proof.
move=> hf hpos hw hs; constructor.
- move=> n; rewrite (@greedy_system_set_identity R X f r A g hs n).
  apply: (@greedy_all_sets_measurable R X mu hm r f _ hf).
  exact: greedy_system_scalar_laws hs.
- exact: greedy_system_characteristic hs.
- move=> x.
  have he : nonnegative_sum setT (fun n => (r n * g n x)%R%:E) =
      nonnegative_sum setT (fun n => (greedy_scalar_term r (f x)
        (fun i => greedy_system_partial_sum r g i x) n)%:E).
    apply: nonnegative_sum_ext=> n _; by rewrite (@greedy_system_term_identity R X f r A g hs n x).
  rewrite he; exact: (@greedy_scalar_series_exact R r (f x) _ hw (hpos x)
    (@greedy_system_scalar_laws R X f r A g hs x)).
Qed.

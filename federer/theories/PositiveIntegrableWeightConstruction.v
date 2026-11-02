(** Private existence construction for the weight supporting Federer (1969),
    2.4.16, p. 90. Source context and specification:
    PositiveIntegrableWeightUP.v. A countable finite-measure cover, positive
    geometric coefficients divided by 1+measure, and the proved
    nonnegative-sum integral theorem produce the witness. Overlaps and null
    cover pieces require no exceptional branch or discarded points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic CountablyMeasurableUP CountablyMeasurableSequences
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureFiniteCharacteristicIntegral DensityCharacteristicIntegral NonnegativeSum
  SequenceSpaceUP SequenceWeights FiniteMeasureWeight TotalNonnegativeSeriesIntegral PositiveIntegrableWeightUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_integrable_weight_exists]: supporting
    positive integrable weight on a countably measurable set for the
    full sign constraint in Federer 2.4.16, p. 90. *)
Theorem positive_integrable_weight_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  measure_countably_measurable mu A -> exists w,
    is_positive_integrable_weight mu A w.
Proof.
move=> hA; have [C [hcover hC]] := (countably_measurable_sequence_iff hm A).1 hA.
have hfin n : mu (C n) \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact (hC n).2.
pose b n := fine (mu (C n)).
have hb n : mu (C n) = (b n)%:E by rewrite /b fineK.
have hb0 n : (0 <= b n)%R by have hh := measure_nonnegative hm (C n); move: hh; rewrite hb lee_fin.
pose c n := finite_measure_weight n (b n).
have hc n := @finite_measure_weight_bounds R n (b n) (hb0 n).
pose s n := @CharacteristicFunction.value R X (C n).
have hs n : is_characteristic_function (C n) (s n) := @CharacteristicFunction.laws R X (C n).
pose u n x := ((c n*s n x)%:E : extended_real_line R).
have hu n x : 0 <= u n x.
  rewrite /u; have [hx|hx] := pselect (C n x).
  - by rewrite (characteristic_on_set (hs n) hx) mulr1 lee_fin; exact: ltW (hc n).1.
  - by rewrite (characteristic_off_set (hs n) hx) mulr0.
have hule n x : u n x <= (@sequence_metric_weight R n)%:E.
  rewrite /u; have [hx|hx] := pselect (C n x).
  - by rewrite (characteristic_on_set (hs n) hx) mulr1 lee_fin; exact (hc n).2.1.
  - rewrite (characteristic_off_set (hs n) hx) mulr0 lee_fin.
    exact: ltW (sequence_metric_weight_positive n).
pose S x := nonnegative_sum setT (fun n => u n x).
have hS0 x : 0 <= S x := nonnegative_sum_nonnegative _ _.
have hS1 x : S x <= 1.
  apply: le_trans (@nonnegative_sum_mono R (Choice.clone nat _) setT
    (fun n => u n x) (fun n => (@sequence_metric_weight R n)%:E) _) (@sequence_metric_weight_sum_bound R).
  by move=> n _; exact: hule.
have hSfin x : S x \is a fin_num.
  rewrite (ge0_fin_numE (hS0 x)); exact: le_lt_trans (hS1 x) (ltry _).
have hSon x : A x -> 0 < S x.
  rewrite hcover; move=> [n _ hx].
  have ht : 0 < u n x.
    by rewrite /u (characteristic_on_set (hs n) hx) mulr1 lte_fin; exact (hc n).1.
  exact: lt_le_trans ht (@nonnegative_sum_term R (Choice.clone nat _) setT (fun n => u n x) n I).
have hSoff x : ~ A x -> S x = 0.
  move=> hx; apply: nonnegative_sum_zero=> n _.
  have hn : ~ C n x by move=> hnx; apply: hx; rewrite hcover; exists n.
  by rewrite /u (characteristic_off_set (hs n) hn) mulr0.
pose J := nonnegative_sum setT (fun n => (c n)%:E*mu (C n)).
have hJ0 : 0 <= J := nonnegative_sum_nonnegative _ _.
have hJ1 : J <= 1.
  apply: le_trans (@nonnegative_sum_mono R (Choice.clone nat _) setT
    (fun n => (c n)%:E*mu (C n)) (fun n => (@sequence_metric_weight R n)%:E) _) (@sequence_metric_weight_sum_bound R).
  move=> n _; rewrite hb -EFinM lee_fin; exact (hc n).2.2.
have hJfin : J \is a fin_num.
  rewrite (ge0_fin_numE hJ0); exact: le_lt_trans hJ1 (ltry _).
have huint n : is_measure_integral mu (partial_function_total (u n)) ((c n)%:E*mu (C n)).
  have hi := @measure_positive_characteristic_integral R X mu hm (C n) (s n) (c n)
    (hs n) (hC n).1 (hc n).1.
  exact: measure_integral_graph_equivalent (real_total_embedding_graph _) hi.
have hSi := @total_nonnegative_series_integral R X mu hm u _ hu huint.
pose w := fun x => (fine (S x) : real_norm_metric_space (scalar_absolute_value_norm R)).
have hw x : (w x)%:E = S x by rewrite /w fineK.
exists w; split.
- move=> x; have hh := hS0 x; by rewrite -hw lee_fin in hh.
- move=> x; have hh := hS1 x; by rewrite -hw lee_fin in hh.
- move=> x; split.
  + move=> hx; have [ha|ha] := pselect (A x); first exact ha.
    have hz : w x = 0%R by rewrite /w (hSoff x ha).
    by move: hx; rewrite hz ltxx.
  + move=> hx; have hh := hSon x hx; by rewrite -hw lte_fin in hh.
- exists (fine J); split; first by move: hJ0; rewrite -(fineK hJfin) lee_fin.
  split; first by move: hJ1; rewrite -(fineK hJfin) lee_fin.
  rewrite (fineK hJfin).
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hSi)=> x z.
  change (S x=z <-> (w x)%:E=z); by rewrite hw.
Qed.

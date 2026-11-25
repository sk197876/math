(** Federer (1969), 2.10.47, p. 204: bound the content of a small set by 2^n
    times one level-j cube cost. This proves the finite-cover part of the
    second printed comparison. The covering sets may repeat; the indexed
    covering inequality handles repetitions. Source context:
    DyadicSmallSetCover.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicSmallSetCover RefiningCoverContent
  MetricDiameter MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport
  CountingConstantSum CountingFinitePredicate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_level_content_bound]: the 2^n
    cost estimate for the covering by H_j cubes in
    2.10.47, p. 204, before substituting the power
    gauge and comparing the two adjacent scales. *)
Theorem dyadic_level_content_bound (R : realType) n (a : R_n R n) Q cost i gamma j
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (b : R) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) cost i gamma ->
  (forall T, refining_cover_tail (dyadic_cube_level Q) i T -> 0<=cost T) ->
  (i<=j)%N -> (0<=b)%R -> (forall s, cost (@Q j s)<=b%:E) ->
  S!=set0 -> (forall x, S x -> forall l, (a l<=x l<=a l+1)%R) ->
  extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E ->
  gamma S<=(((2^n)%N)%:R*b)%:E.
Proof.
move=> hQ hg hc hij hb hcost hne hroot hdiam.
have hm := refining_cover_content_measure hg hc.
have [F hF] := @dyadic_small_set_cover R n a Q j S hQ hne hroot hdiam.
have hgen s : gamma (@Q j s)<=b%:E.
  have ht : refining_cover_tail (dyadic_cube_level Q) i (@Q j s).
    exists j; split=> //; by exists s.
  exact: le_trans (refining_cover_content_generator hg ht (hc _ ht)) (hcost s).
apply: le_trans (@measure_indexed_cover R _ [the choiceType of {ffun 'I_n -> bool}] gamma hm
  S setT (fun z=>@Q j (F z)) (finite_set_countable (@finite_finset _ setT)) hF) _.
have hsum : nonnegative_sum setT (fun z : {ffun 'I_n -> bool}=>gamma (@Q j (F z)))<=
    nonnegative_sum setT (fun _ : {ffun 'I_n -> bool}=>b%:E).
  apply: nonnegative_sum_mono=> z _; exact: hgen.
apply: le_trans hsum _.
rewrite (nonnegative_constant_sum_counting _ hb) counting_finite_whole
  dyadic_binary_choice_count -EFinM mulrC.
exact: lexx.
Qed.

(** Federer (1969), 3.2.37, p. 274: actual positive-degree
    upper and lower contents fail the countable-cover measure law.
    The degree-zero case, for which both are counting measure,
    is stated separately rather than suppressed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  MinkowskiContents FinitePositiveMinkowskiContent DenseMinkowskiInfinite
  MinkowskiZeroCounting CountingMeasure MeasureUP MeasureIndexedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_minkowski_singletons_zero]: the singleton
    side of the non-measure assertion in Federer 3.2.37, p. 274.
    Actual positive natural degrees are required, and the source
    may be any point of its Euclidean ambient space. *)
Lemma positive_minkowski_singletons_zero (R:realType) n m
    (x:inner_metric_space (@euclidean_inner_productP R n)):
  (0<m)%N ->(m<=n)%N ->
  upper_minkowski_content m [set x]=0 /\lower_minkowski_content m [set x]=0.
Proof.
move=>hm hmn.
have h:=finite_positive_minkowski_contents (R:=R) [fset x] hm hmn.
have hSet:[set` [fset x]]=[set x].
  apply/seteqP; split=>y.
  - move=>hy; have hy':y \in [fset x]:=hy.
    move/fset1P:hy'=>hy'; exact:hy'.
  - move=>->; change (x \in [fset x]); by rewrite inE.
by rewrite hSet in h.
Qed.

(** Source for [positive_minkowski_contents_not_measures]: a proved
    example for both non-measure assertions in Federer 3.2.37,
    p. 274. A countable dense original source has both contents
    infinite but is covered by its null singletons. This proves
    failure of the actual project's measure law, and imposes no
    measurability or finite-content premise on the source. *)
Theorem positive_minkowski_contents_not_measures (R:realType) n m:
  (0<m)%N ->(m<=n)%N ->
  exists D:set (inner_metric_space (@euclidean_inner_productP R n)),
    [/\ countable D,dense D,
      upper_minkowski_content m D= +oo,
      lower_minkowski_content m D= +oo &
      ~is_measure (@upper_minkowski_content R n m) /\
      ~is_measure (@lower_minkowski_content R n m)].
Proof.
move=>hm hmn.
have hn:(0<n)%N:=leq_trans hm hmn.
have [D [hCountable hDense]]:=euclidean_metric_separable R n.
have [hUpper hLower]:=@dense_minkowski_contents_infinite R n m D hn hDense.
have hNoMeasure (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):
    (forall x,mu [set x]=0) ->mu D= +oo ->~is_measure mu.
  move=>hAtoms hInfinity hMeasure.
  have hCover:mu D<=nonnegative_sum D (fun x=>mu [set x]).
    apply:(@measure_indexed_cover R
      (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R n)) mu hMeasure D D
      (fun x=>[set x]) hCountable).
    by move=>x hx; exists x.
  have hSum:nonnegative_sum D (fun x=>mu [set x])=0.
    apply:nonnegative_sum_zero=>x _; exact:hAtoms.
  rewrite hInfinity hSum in hCover.
  by rewrite leNgt ltry in hCover.
exists D; split=>//; split.
- apply:hNoMeasure; last exact:hUpper.
  move=>x; exact:(positive_minkowski_singletons_zero x hm hmn).1.
- apply:hNoMeasure; last exact:hLower.
  move=>x; exact:(positive_minkowski_singletons_zero x hm hmn).2.
Qed.

(** Source for [zero_minkowski_contents_are_measures]: the proved
    degree-zero qualification to the non-measure sentence of
    Federer 3.2.37, p. 274. Both actual functions are the existing
    counting measure, including the positive ambient-zero atom. *)
Corollary zero_minkowski_contents_are_measures (R:realType) n:
  is_measure (@upper_minkowski_content R n 0) /\
  is_measure (@lower_minkowski_content R n 0).
Proof.
have hUpper:@upper_minkowski_content R n 0=@counting_measure R _.
  apply:funext=>S; exact:(zero_minkowski_contents_counting S).1.
have hLower:@lower_minkowski_content R n 0=@counting_measure R _.
  apply:funext=>S; exact:(zero_minkowski_contents_counting S).2.
rewrite hUpper hLower; split; exact:counting_measure_is_measure.
Qed.

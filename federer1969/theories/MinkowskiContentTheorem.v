(** Federer (1969), 3.2.37, pp. 273--274: the complete
    Minkowski-content item, including the compact-family Gross
    characterization. Degree zero is retained and proved to be
    counting measure; the printed non-measure sentence therefore
    requires positive degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoordinateProjection MinkowskiContents MinkowskiContentsBasic
  LowerMinkowskiProjectionBound GrossLowerMinkowskiBound GrossCompactProjectionSupremum
  CompactProjectionFamilyUP MinkowskiZeroCounting MinkowskiNonmeasure
  CountingMeasure ProjectionMeasure MeasureUP PartialFunctionUP TopologicalBorel ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_37]: all assertions in Federer
    3.2.37, pp. 273--274. Upper and lower contents use actual
    whole positive-radius tubes; their common partial value exists
    exactly on agreement. Both are nonnegative, ordered and closure
    invariant. The lower content dominates every actual orthogonal
    projection volume and Gross measure on every original source.
    The printed finite-compact-family supremum is proved on every
    Borel source. Positive-degree contents fail the actual countable
    measure law; degree-zero contents instead equal counting measure.
    Arbitrary nonmeasurable and unbounded sources, infinite values,
    empty sets, zero normal blocks and positive zero-degree atoms remain. *)
Theorem federer_3_2_37 (R:realType) n m (hmn:(m<=n)%N):
  (forall (S:set (inner_metric_space (@euclidean_inner_productP R n))) y,
    partial_function_graph (@minkowski_content R n m) S y <->
      upper_minkowski_content m S=y /\lower_minkowski_content m S=y) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)),
    0<=lower_minkowski_content m S /\lower_minkowski_content m S<=upper_minkowski_content m S) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)),
    upper_minkowski_content m (closure S)=upper_minkowski_content m S /\
    lower_minkowski_content m (closure S)=lower_minkowski_content m S) /\
  (forall (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:{linear R_n R n->R_n R m}),O_star p ->
      @euclidean_lebesgue_measure R m (p @` S)<=lower_minkowski_content m S) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)),
    @gross_measure R n m S<=lower_minkowski_content m S) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)),borel_set S ->
    is_extended_real_supremum (compact_projected_family_values m S) (@gross_measure R n m S)) /\
  ((0<m)%N ->~is_measure (@upper_minkowski_content R n m) /\
    ~is_measure (@lower_minkowski_content R n m)) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)),
    upper_minkowski_content 0 S=@counting_measure R _ S /\
    lower_minkowski_content 0 S=@counting_measure R _ S).
Proof.
split; first exact:minkowski_content_graph.
split.
- move=>S; split; first exact:(minkowski_contents_nonnegative m S).1.
  exact:minkowski_contents_ordered.
split; first exact:minkowski_contents_closure.
split; first by move=>S p hp; exact:lower_minkowski_projection_bound hmn hp.
split; first by move=>S; exact:gross_measure_lower_minkowski_bound hmn.
split; first by move=>S hS; exact:gross_measure_compact_projection_supremum hmn hS.
split; last exact:zero_minkowski_contents_counting.
move=>hm; have [D [_ _ _ _ hFailure]]:=@positive_minkowski_contents_not_measures R n m hm hmn.
exact:hFailure.
Qed.

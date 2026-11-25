(** Federer (1969), 2.3.6, p. 77, final observation: a dense subset of Ulam
    cardinality suffices in Lusin's theorem. Source context:
    MeasurableFiniteImageSupport.v. The empty target and empty-support cases
    yield a null A and are treated separately; no inhabitance assumption is
    added to this conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground PartialFunctionUP PartialContinuityUP
  PartialContinuityTotal MeasureUP MeasureBasic MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalExtension MeasureRestriction MeasurePushforward MeasureSupport UlamCardinalUP
  MeasurableFiniteImageSupport LusinApproximationUP LusinRangeTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_null_source_set]: supporting null-set
    boundary for the range reduction in Federer 2.3.6, p. 77.
    The empty closed or compact set is a valid continuity set. *)
Lemma lusin_null_source_set (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (P : set (set X)) (A : set X)
    (f : partial_function X Y) (e : R) : P set0 -> mu A = 0 -> (0 < e)%R ->
  exists C, P C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
Proof.
move=> hp hz he; exists set0; split=> //; split; first by move=> x [].
split; first by rewrite setD0 hz lte_fin.
exact: partial_continuity_empty.
Qed.

(** Source for [lusin_ulam_dense_range]: direct range extension
    in Federer 2.3.6, p. 77, expressed simultaneously for
    the closed and compact conclusions. The support and its
    concentration/separability follow from the project's 2.2.16. *)
Theorem lusin_ulam_dense_range (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu) (P : set (set X))
    (D : set Y) (A : set X) (f : partial_function X Y) (e : R) :
  P set0 -> has_lusin_approximation mu P -> dense D -> is_ulam_set R D ->
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < e)%R -> exists C, P C /\ C `<=` A /\ mu (A `\` C) < e%:E /\
    partial_function_continuous_on C f.
Proof.
move=> hp hL hd hu hf hA hfin he.
case: (pselect (exists y : Y, True))=> [[y0 _]|hnY].
- have [g [hfg [ha hg]]] := @measurable_function_total_extension R X Y mu hm f y0 hf.
  pose S := measure_support (measure_pushforward g (measure_restrict mu A)).
  have [hS [[H [hc hH]] hnull]] := @measurable_finite_image_support R X Y mu hm g A D hg hfin hd hu.
  case: (pselect (S !=set0))=> [[s hs]|hnS].
  + pose s0 : metric_subset S := Sub s (mem_set hs).
    exact (@lusin_closed_separable_range_transfer R X Y mu hm P f g A S s0 H e
      hL hf hfg hg hA hfin hS hc hH hnull he).
  + have hS0 : S = set0.
      apply/seteqP; split=> s // hs; apply: hnS; by exists s.
    have hz : mu A = 0.
      change (mu (A `&` (g @^-1` (~` S))) = 0) in hnull.
      by rewrite hS0 setC0 preimage_setT setIT in hnull.
    exact: (@lusin_null_source_set R X Y mu P A f e hp hz he).
- have hz : mu A = 0.
    apply: (@measure_null_subset R X mu hm A (~` partial_function_domain f)).
    + move=> x _ [y _]; apply: hnY; by exists y.
    + exact: measurable_function_domain hf.
  exact: (@lusin_null_source_set R X Y mu P A f e hp hz he).
Qed.

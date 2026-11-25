(** Federer (1969), 3.1.4, pp. 214–215: refine the
    printed C cutoffs by the conull set where their translated
    slices are measurable. They still exhaust B up to a null set,
    and every retained point satisfies the actual S_i mass bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions ApproximatePartialUniformCutoffs EuclideanPrefixCutoffs
  CoordinateSectionGoodBases CoordinateExceptionalMass ApproximateCoordinateExceptionalSets
  EuclideanSmallMassCutoffs RealMetricBackground PartialFunctionBasic
  MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Cutoffs.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Variables f g : X -> R^o.
Variables e c : R.
Variable p : nat.
Local Notation B := (approximate_partial_uniform_cutoff i f g e c p).

(** Source for [coordinate_measurable_slice_cutoff]: the C cutoff
    of Federer 3.1.4, p. 214, refined by a conull measurable set
    to justify each Fubini calculation on p. 215. This refinement
    imposes no new hypothesis on f and loses only a null set. *)
Definition coordinate_measurable_slice_cutoff q : set X :=
  (@prefix_slice_uniform_cutoff R m i B g e c q) `&`
    coordinate_section_good_bases i f g B.

(** Source for [coordinate_measurable_slice_cutoff_subset]:
    C is contained in B in Federer 3.1.4, p. 214. *)
Lemma coordinate_measurable_slice_cutoff_subset q :
  coordinate_measurable_slice_cutoff q `<=` B.
Proof. by move=> a [[ha _] _]. Qed.

(** Source for [coordinate_measurable_slice_cutoff_increasing]:
    monotonicity in q, Federer 3.1.4, p. 215; the
    fixed conull refinement preserves it. *)
Lemma coordinate_measurable_slice_cutoff_increasing q r :
  (q<=r)%N -> coordinate_measurable_slice_cutoff q `<=`
    coordinate_measurable_slice_cutoff r.
Proof.
move=> hqr a [ha hG]; split=> //.
exact: (@prefix_slice_uniform_cutoff_increasing R m i B g e c q r hqr a ha).
Qed.

(** Source for [coordinate_measurable_slice_cutoff_measurable]:
    measurable C sets in Federer 3.1.4, p. 215,
    including the measurable conull slice qualification. *)
Lemma coordinate_measurable_slice_cutoff_measurable q :
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) ->
  measure_measurable (@euclidean_lebesgue_measure R m) (coordinate_measurable_slice_cutoff q).
Proof.
move=> hf hg.
have hB := @approximate_partial_uniform_cutoff_measurable R m i f g e c p hf hg.
apply: (measure_measurable_intersection (euclidean_lebesgue_is_measure R m)).
- exact: (@prefix_slice_uniform_cutoff_measurable R m i B g e c q (leqW (ltn_ord i)) hB hg).
- exact: (@coordinate_section_good_bases_measurable R m i f g B hf hg hB).
Qed.

(** Source for [coordinate_measurable_slice_cutoffs_conull]:
    the C exhaustion in Federer 3.1.4, p. 215,
    remains conull after excluding the bad affine restrictions. *)
Theorem coordinate_measurable_slice_cutoffs_conull :
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) -> 0<e -> 0<c ->
  euclidean_lebesgue_measure m
    (B `\` \bigcup_q coordinate_measurable_slice_cutoff q)=0%E.
Proof.
move=> hf hg he hc.
have hB := @approximate_partial_uniform_cutoff_measurable R m i f g e c p hf hg.
have hnC := @prefix_slice_uniform_cutoffs_conull R m i B g e c (leqW (ltn_ord i)) hB hg he hc.
have hnG := @coordinate_section_good_bases_conull R m i f g B hf hg hB.
have hnull := measure_null_union (euclidean_lebesgue_is_measure R m) hnC hnG.
apply: (@measure_null_subset R [the choiceType of X] (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) _ _ _ hnull)=> a [ha hn].
case: (pselect (coordinate_section_good_bases i f g B a))=> [hG|hG].
- left; split=> //; move=> [q _ hq]; apply: hn.
  exists q=> //; by split.
- by right.
Qed.

(** Source for [coordinate_measurable_slice_cutoff_mass]:
    derive the bound L^m(S_i)<=2^(m+1) r^m/j in
    Federer 3.1.4, p. 215, from the B and C laws.
    It is proved for arbitrary nonnegative mass coefficient c. *)
Theorem coordinate_measurable_slice_cutoff_mass a q r :
  0<=c -> coordinate_measurable_slice_cutoff q a ->
  0<r -> r<(p.+1%:R)^-1 -> r<(q.+1%:R)^-1 ->
  (euclidean_lebesgue_measure m
    (coordinate_staircase_exception f (fun _=>g) a e i
      `&` metric_closed_ball (0%R : X) r)
    <=(2^+(m+1)*c*r^+m)%R%:E)%E.
Proof.
move=> hc [[hBa hC] hG] hr hrp hrq.
apply: (@coordinate_exceptional_mass_from_sections R m i f g a B e c r
  hc (ltW hr) hG).
- exact: hC r hr hrq.
- move=> x hx; have hb := hx.2 r hr hrp.
  by rewrite expr1 in hb.
Qed.
End Cutoffs.

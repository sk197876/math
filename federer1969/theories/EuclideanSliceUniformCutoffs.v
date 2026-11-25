(** Federer (1969), 3.1.4, pp. 214–215: measurable increasing
    prefix-shift cutoffs C have conull union in B. The corrected
    weak derivative-variation threshold is retained in Z. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground PartialFunctionBasic MeasureUP MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  EuclideanSliceVariationSets EuclideanSliceVariationDensity EuclideanSmallMassCutoffs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SliceCutoffs.
Variable R : realType.
Variables k l : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R (k+l))).
Local Notation Leb := (@euclidean_lebesgue_measure R (k+l)).
Variable B : set X.
Variable g : X -> R^o.
Variables e c : R.

(** Source for [euclidean_slice_uniform_cutoff]: C(i,j,p,q)
    in Federer 3.1.4, p. 214, with B fixed. Taking e=c=1/j,
    k=i-1 and the positive index q+1 gives the printed tolerances.
    Closed radius sections give the auxiliary stronger bound. *)
Definition euclidean_slice_uniform_cutoff q : set X :=
  B `&` euclidean_small_mass_cutoff (euclidean_slice_variation_exception B g e) c q.

(** Source for [euclidean_slice_uniform_cutoff_increasing]:
    monotonicity in q asserted in Federer 3.1.4, p. 215. *)
Lemma euclidean_slice_uniform_cutoff_increasing p q :
  (p<=q)%N -> euclidean_slice_uniform_cutoff p `<=` euclidean_slice_uniform_cutoff q.
Proof.
move=> hpq x [hx hb]; split=> //; exact: (@euclidean_small_mass_cutoff_increasing R (k+l) k (euclidean_slice_variation_exception B g e) c p q hpq x hb).
Qed.

(** Source for [euclidean_slice_uniform_cutoff_measurable]:
    measurability of C asserted in Federer 3.1.4, p. 215,
    using the corrected Z family and 3.1.3(1). *)
Lemma euclidean_slice_uniform_cutoff_measurable q :
  measure_measurable Leb B ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb (partial_function_total g) ->
  measure_measurable Leb (euclidean_slice_uniform_cutoff q).
Proof.
move=> hB hg; apply: (measure_measurable_intersection (euclidean_lebesgue_is_measure R (k+l)) hB).
apply: euclidean_small_mass_cutoff_measurable.
exact: euclidean_slice_variation_exception_measurable hB hg.
Qed.

(** Source for [euclidean_slice_uniform_cutoffs_conull]:
    L^m(B minus union_q C)=0, Federer 3.1.4, p. 215.
    The countable radius exhaustion follows from 3.1.3(4),(5). *)
Theorem euclidean_slice_uniform_cutoffs_conull :
  measure_measurable Leb B ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb (partial_function_total g) ->
  0<e -> 0<c ->
  Leb (B `\` \bigcup_q euclidean_slice_uniform_cutoff q)=0%E.
Proof.
move=> hB hg he hc.
have hz := euclidean_almost_slice_variation_density_zero hB hg he.
apply: (@measure_null_subset R [the choiceType of X] Leb
  (euclidean_lebesgue_is_measure R (k+l)) _ _ _ hz)=> x [hx hn].
split=> //; move=> hd.
have [q hq] := euclidean_zero_density_has_small_mass_cutoff hc hd.
apply: hn; exists q=> //; by split.
Qed.
End SliceCutoffs.

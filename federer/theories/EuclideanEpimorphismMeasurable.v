(** Federer (1969), 3.1.3(3), p. 213: inverse images of Lebesgue
    measurable sets under linear epimorphisms are Lebesgue measurable.
    The proof uses the sealed adapted chart, a measurable product cylinder,
    and the change-of-variables result of 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLinearMaps EuclideanLebesgueDeterminant
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanEpimorphismChartUP
  EuclideanEpimorphismChartSealed MeasureUP MeasureBasic MeasureSplit MeasurePushforward
  PushforwardMeasurabilityTransfer ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_automorphism_preimage_measurable]: the
    invertible-linear part of the proof of Federer 3.1.3(3), p. 213,
    using the determinant formula of 2.7.16, pp. 134–135. *)
Lemma euclidean_automorphism_preimage_measurable (R : realType) n
    (f g : {linear R_n R n -> R_n R n})
    (W : set (inner_metric_space (@euclidean_inner_productP R n))) :
  cancel f g -> measure_measurable (@euclidean_lebesgue_measure R n) W ->
  measure_measurable (@euclidean_lebesgue_measure R n) (f @^-1` W).
Proof.
move=> hfg hW; have hf := can_inj hfg.
have hd := (euclidean_det_injective f).2 hf.
apply: measure_pushforward_preimage_measurable hf _.
move=> T; rewrite /measure_pushforward !euclidean_lebesgue_linear_pushforward //
  (hW T) ge0_muleDr //.
all: exact: (@measure_nonnegative R _ _ (euclidean_lebesgue_is_measure R n)).
Qed.

(** Source for [euclidean_epimorphism_block_preimage_measurable]:
    beta identifies alpha^-1(W) with W times R^k in Federer 3.1.3(3),
    p. 213. This block form includes zero-dimensional factors. *)
Lemma euclidean_epimorphism_block_preimage_measurable (R : realType) m k
    (p : {linear R_n R (m+k) -> R_n R m})
    (W : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (forall y, exists x, p x=y) ->
  measure_measurable (@euclidean_lebesgue_measure R m) W ->
  measure_measurable (@euclidean_lebesgue_measure R (m+k)) (p @^-1` W).
Proof.
move=> hp hW.
have hc := @EuclideanEpimorphismChart.laws R (m+k) m p hp.
case: (@EuclideanEpimorphismChart.value R (m+k) m p hp) hc=> hmn [f g] hc /=.
have hfg := epimorphism_chart_forward_inverse hc.
have hfirst x : (euclidean_block_split (f x)).1=p x.
  apply/ffunP=> i; rewrite /euclidean_block_split /= ffunE.
  have hi : lshift k i=widen_ord hmn i by apply: val_inj.
  by rewrite hi (epimorphism_chart_coordinates hc).
have hC : measure_measurable
    (product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R k))
    (W `*` setT).
  exact: (product_measure_measurable_rectangle (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k) hW
    (measure_measurable_whole (euclidean_lebesgue_is_measure R k))).1.
have hB : measure_measurable (@euclidean_lebesgue_measure R (m+k))
    ((@euclidean_block_split R m k) @^-1` (W `*` setT)).
  apply: measure_pushforward_preimage_measurable (can_inj (@euclidean_block_splitK R m k)) _.
  by rewrite euclidean_block_measure.
have hpre : p @^-1` W=f @^-1` ((@euclidean_block_split R m k) @^-1` (W `*` setT)).
  apply/seteqP; split=> x hx.
  - split; last exact Logic.I; by rewrite hfirst.
  - move: hx=> [hx _]; by rewrite hfirst in hx.
rewrite hpre; exact: euclidean_automorphism_preimage_measurable hfg hB.
Qed.

(** Source for [euclidean_epimorphism_preimage_measurable]: the whole
    assertion (3) in Federer 3.1.3, p. 213. Surjectivity proves the
    required dimension inequality; no extra dimension hypothesis is imposed. *)
Theorem euclidean_epimorphism_preimage_measurable (R : realType) n m
    (p : {linear R_n R n -> R_n R m})
    (W : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (forall y, exists x, p x=y) ->
  measure_measurable (@euclidean_lebesgue_measure R m) W ->
  measure_measurable (@euclidean_lebesgue_measure R n) (p @^-1` W).
Proof.
move=> hp hW.
have hmn := projT1 (@EuclideanEpimorphismChart.value R n m p hp).
have hn : n=(m+(n-m))%N by rewrite addnC subnK.
move: p hp; rewrite hn=> p hp.
exact: euclidean_epimorphism_block_preimage_measurable hp hW.
Qed.

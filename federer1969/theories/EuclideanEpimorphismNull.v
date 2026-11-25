(** Federer (1969), 3.1.3(3)–(4), p. 213: the adapted linear
    chart also preserves nullity under inverse image. This supplies
    the conull-domain part of the measurable composition in (4). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLinearMaps EuclideanLebesgueDeterminant
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanEpimorphismChartUP
  EuclideanEpimorphismChartSealed EuclideanEpimorphismMeasurable
  MeasureUP MeasureSplit MeasureFiniteClosure MeasurePushforward ProductMeasure ProductRectangleValue
  PartialFunctionUP PartialFunctionPrecomposition MeasureAlmostUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_epimorphism_block_preimage_null]: supporting
    null-cylinder case of the chart argument in Federer 3.1.3(3),
    p. 213. It uses zero times infinity equals zero as in 2.6.2(2). *)
Lemma euclidean_epimorphism_block_preimage_null (R : realType) m k
    (p : {linear R_n R (m+k) -> R_n R m})
    (N : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (forall y, exists x, p x=y) -> @euclidean_lebesgue_measure R m N=0%E ->
  @euclidean_lebesgue_measure R (m+k) (p @^-1` N)=0%E.
Proof.
move=> hp hN.
have hc := @EuclideanEpimorphismChart.laws R (m+k) m p hp.
case: (@EuclideanEpimorphismChart.value R (m+k) m p hp) hc=> hmn [f g] hc /=.
have hfg := epimorphism_chart_forward_inverse hc.
have hfirst x : (euclidean_block_split (f x)).1=p x.
  apply/ffunP=> i; rewrite /euclidean_block_split /= ffunE.
  have hi : lshift k i=widen_ord hmn i by apply: val_inj.
  by rewrite hi (epimorphism_chart_coordinates hc).
have hC : product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k) (N `*` setT)=0%E.
  have hNm := measure_null_measurable (euclidean_lebesgue_is_measure R m) hN.
  have hCt := product_measure_rectangle_value (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k) hNm
    (measure_measurable_whole (euclidean_lebesgue_is_measure R k)).
  by rewrite hN mul0e in hCt.
have hB : @euclidean_lebesgue_measure R (m+k)
    ((@euclidean_block_split R m k) @^-1` (N `*` setT))=0%E.
  change (measure_pushforward (@euclidean_block_split R m k)
    (@euclidean_lebesgue_measure R (m+k)) (N `*` setT)=0%E).
  by rewrite euclidean_block_measure.
have hpre : p @^-1` N=f @^-1` ((@euclidean_block_split R m k) @^-1` (N `*` setT)).
  apply/seteqP; split=> x hx.
  - split; last exact Logic.I; by rewrite hfirst.
  - move: hx=> [hx _]; by rewrite hfirst in hx.
rewrite hpre euclidean_lebesgue_linear_pushforward; last exact: (euclidean_det_injective f).2 (can_inj hfg).
by rewrite hB mule0.
Qed.

(** Source for [euclidean_epimorphism_preimage_null]: supporting
    nullity under a linear epimorphism in Federer 3.1.3(3)–(4),
    p. 213. This also proves preservation of conull partial domains. *)
Theorem euclidean_epimorphism_preimage_null (R : realType) n m
    (p : {linear R_n R n -> R_n R m})
    (N : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (forall y, exists x, p x=y) -> @euclidean_lebesgue_measure R m N=0%E ->
  @euclidean_lebesgue_measure R n (p @^-1` N)=0%E.
Proof.
move=> hp hN.
have hmn := projT1 (@EuclideanEpimorphismChart.value R n m p hp).
have hn : n=(m+(n-m))%N by rewrite addnC subnK.
move: p hp; rewrite hn=> p hp.
exact: euclidean_epimorphism_block_preimage_null hp hN.
Qed.

(** Source for [euclidean_epimorphism_measurable_precompose]: the
    composition g o alpha in Federer 3.1.3(4), p. 213, by (3).
    The target may be any topological space. Actual partial domains
    are pulled back, and their complements remain null. *)
Theorem euclidean_epimorphism_measurable_precompose (R : realType) n m
    (Y : topologicalType) (p : {linear R_n R n -> R_n R m})
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R m)) Y) :
  (forall y, exists x, p x=y) -> is_measure_measurable_function (@euclidean_lebesgue_measure R m) f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R n) (partial_function_precompose p f).
Proof.
move=> hp hf; constructor.
- rewrite /measure_almost_everywhere partial_function_precompose_domain preimage_setC.
  exact: euclidean_epimorphism_preimage_null hp (measurable_function_domain hf).
- move=> W hW; rewrite partial_function_precompose_preimage.
  exact: euclidean_epimorphism_preimage_measurable hp (measurable_function_open_preimage hf hW).
Qed.

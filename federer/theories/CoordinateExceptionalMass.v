(** Federer (1969), 3.1.4, p. 215: the quantitative
    exceptional-set estimate, obtained from the actual scalar sections
    and corrected prefix variation set. The final constant is 2^(m+1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanPrefixTranslation EuclideanPrefixCutoffs
  CoordinateSectionGoodBases CoordinatePrefixExceptionalSets PrefixCylinderAdapters
  CoordinateRemainderSetMeasurable ApproximateCoordinateExceptionalSets
  EuclideanExceptionalSectionEstimate EuclideanBlockCoordinates EuclideanBlockMeasure
  ProductMeasure ProductSections CountablyMeasurableUP CountablyMeasurableSubsets
  CountablyMeasurableProduct MeasureUP MeasureBasic MeasurePushforward
  PushforwardMeasurabilityTransfer MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [coordinate_exception_coefficient_bound]:
    the last numerical bound on the measure of S_i in
    Federer 3.1.4, p. 215. Indices here start at zero. *)
Lemma coordinate_exception_coefficient_bound (R : realType) m (i : 'I_m) :
  (2+2^+i)*2^+(m-(i+1))<=(2 : R)^+(m+1).
Proof.
have hi : (i+1<=m)%N by rewrite addn1; exact: ltn_ord.
have hdim : (m+1)%N=((i+1)+1+(m-(i+1)))%N.
  by rewrite addnAC (subnKC hi).
have hpow j : 1<=(2 : R)^+j.
  elim: j=> [|j hj]; first by rewrite expr0.
  rewrite exprS; nra.
rewrite hdim exprD.
apply: ler_wpM2r; first by rewrite exprn_ge0 // ler0n.
rewrite !addn1 !exprS.
have hp := hpow i; nra.
Qed.

Section ExceptionalMass.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables f g : E m -> R^o.
Variable a : E m.
Variable B : set (E m).
Variables e c r : R.
Local Notation Z := (product_vertical_section
  (@prefix_slice_variation_exception R m i B g e) a).
Local Notation S := (@coordinate_prefix_exception_product R m i f g a e B r).

(** Source for [coordinate_prefix_exception_product_estimate]:
    the two-part Fubini estimate for S_i in Federer 3.1.4,
    p. 215. Outside Z, membership in B supplies the scalar
    section bound; no section estimate is assumed elsewhere. *)
Theorem coordinate_prefix_exception_product_estimate :
  0<=c -> 0<=r ->
  coordinate_section_good_bases i f g B a ->
  (euclidean_lebesgue_measure i
    (Z `&` metric_closed_ball (0%R : E i) r)<=(c*r^+i)%R%:E)%E ->
  (forall x, B x ->
    (euclidean_lebesgue_measure 1%N
      (product_vertical_section (coordinate_remainder_exception_set i f g e) x
        `&` metric_closed_ball (0%R : E 1%N) r)<=(c*r)%R%:E)%E) ->
  (product_measure (euclidean_lebesgue_is_measure R i)
    (euclidean_lebesgue_is_measure R 1) S
    <=((2+2^+i)*c*r^+i.+1)%R%:E)%E.
Proof.
move=> hc hr hgood hZ hT.
have hmS := @coordinate_prefix_exception_product_measurable R m i f g a e B r hgood.
have hcS : measure_countably_measurable
    (product_measure (euclidean_lebesgue_is_measure R i)
      (euclidean_lebesgue_is_measure R 1)) S.
  apply: (measurable_subset_countably_measurable
    (product_measure_is_measure (euclidean_lebesgue_is_measure R i)
      (euclidean_lebesgue_is_measure R 1)) hmS (fun _ _=>Logic.I)).
  exact: product_whole_countably_measurable
    (euclidean_lebesgue_countably_measurable R i)
    (euclidean_lebesgue_countably_measurable R 1).
apply: (@euclidean_exceptional_section_estimate R i S Z c r hc hr hcS).
- exact: (@coordinate_good_base_variation_measurable R m i f g B a e hgood).
- by move=> ut [hball _].
- by rewrite setIC.
- move=> u hu hnZ.
  have hBu : B (@euclidean_prefix_translation R m i a u).
    apply: contrapT=> hn; apply: hnZ; by left.
  apply: le_trans _ (hT _ hBu).
  apply: (measure_mono (euclidean_lebesgue_is_measure R 1)).
  move=> t [[_ ht] [hz|hrem]].
  + by exfalso; exact: hnZ hz.1.
  + split=> //; exact: (@coordinate_prefix_remainder_as_section R m i f g a e u t).1 hrem.
Qed.

(** Source for [coordinate_exceptional_mass_from_sections]:
    the full S_i mass bound on R^m in Federer 3.1.4, p. 215.
    The bound is derived from the actual Z and T estimates, through
    the usual block product identity and a containing cylinder. *)
Theorem coordinate_exceptional_mass_from_sections :
  0<=c -> 0<=r ->
  coordinate_section_good_bases i f g B a ->
  (euclidean_lebesgue_measure i
    (Z `&` metric_closed_ball (0%R : E i) r)<=(c*r^+i)%R%:E)%E ->
  (forall x, B x ->
    (euclidean_lebesgue_measure 1%N
      (product_vertical_section (coordinate_remainder_exception_set i f g e) x
        `&` metric_closed_ball (0%R : E 1%N) r)<=(c*r)%R%:E)%E) ->
  (euclidean_lebesgue_measure m
    (coordinate_staircase_exception f (fun _=>g) a e i
      `&` metric_closed_ball (0%R : E m) r)
    <=(2^+(m+1)*c*r^+m)%R%:E)%E.
Proof.
move=> hc hr hgood hZ hT.
pose S1 := (@euclidean_block_split R i 1) @^-1` S.
have hS := @coordinate_prefix_exception_product_measurable R m i f g a e B r hgood.
have hS1 : measure_measurable (@euclidean_lebesgue_measure R (i+1)) S1.
  apply: measure_pushforward_preimage_measurable
    (can_inj (@euclidean_block_splitK R i 1)) _.
  by rewrite euclidean_block_measure.
have hprod := coordinate_prefix_exception_product_estimate hc hr hgood hZ hT.
have hmass1 : (euclidean_lebesgue_measure (i+1) S1
    <=(((2+2^+i)*c)*r^+(i+1))%R%:E)%E.
  change (measure_pushforward (@euclidean_block_split R i 1)
    (@euclidean_lebesgue_measure R (i+1)) S
    <=(((2+2^+i)*c)*r^+(i+1))%R%:E)%E.
  by rewrite euclidean_block_measure addn1.
have hi : (i<=m)%N := leqW (ltn_ord i).
have hj : (i+1<=m)%N by rewrite addn1; exact: ltn_ord.
pose T := coordinate_staircase_exception f (fun _=>g) a e i
  `&` metric_closed_ball (0 : E m) r.
have hball : T `<=` metric_closed_ball (0 : E m) r by move=> h [_ hh].
have hprefix h : T h -> S1 (euclidean_prefix_restriction hj h).
  move=> [hex hh].
  exact: (@coordinate_staircase_exception_prefix_cover R m i f g a e B r hi hj h hex hh).
have hbound := @euclidean_prefix_restriction_cylinder_bound R m (i+1) hj
  T S1 ((2+2^+i)*c) r hr hS1 hmass1 hball hprefix.
apply: le_trans hbound _; rewrite lee_fin.
have hcoef := @coordinate_exception_coefficient_bound R m i.
have hp : 0<=c*r^+m by rewrite mulr_ge0 // exprn_ge0.
have hb : ((2+2^+i)*2^+(m-(i+1)))*(c*r^+m)
    <=2^+(m+1)*(c*r^+m).
  apply: ler_wpM2r=> //.
have hleft : ((2+2^+i)*c)*2^+(m-(i+1))*r^+m=
    ((2+2^+i)*2^+(m-(i+1)))*(c*r^+m) by ring.
have hright : 2^+(m+1)*c*r^+m = 2^+(m+1)*(c*r^+m) by ring.
by rewrite hleft hright.
Qed.
End ExceptionalMass.

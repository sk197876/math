(** Supporting the final null-image criterion of Federer (1969), 2.10.13, p.
    177. For the image-cost construction of 2.10.10, p. 176, its restriction
    is absolutely continuous exactly when every reference-null subset has
    null image. Use Borel hulls for the arbitrary null sets quantified in
    2.9.2, p. 153, and the partition formula of 2.10.8, p. 175. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BorelFamilyBasic MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction
  MeasureAbsoluteContinuity BorelRegularMeasureUP TopologicalBorel BorelImageCoverCost
  BorelImageMeasureBounds BorelCaratheodoryMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [image_null_absolute_continuity]: supporting
    equivalence for the last sentence of 2.10.13, p. 177.
    The reference measure is any Borel regular measure on a
    separable metric space. Quantification is over all subsets,
    not just measurable sets; continuity of the map is unnecessary
    for this covering-measure statement. *)
Theorem image_null_absolute_continuity (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (lambda : set X -> \bar R) (D A : set X) :
  is_measure beta -> is_measure lambda -> is_borel_regular_measure lambda ->
  countable D -> dense D -> borel_set A ->
  (is_absolutely_continuous_measure
    (measure_restrict (borel_caratheodory_measure (borel_image_cover_cost f beta)) A) lambda <->
    forall T, T `<=` A -> lambda T=0 -> beta (f @` T)=0).
Proof.
move=> hb hl hrl hD hden hA.
pose c := borel_image_cover_cost f beta.
pose mu := borel_caratheodory_measure c.
have hm := borel_caratheodory_is_measure (borel_image_cover_cost_laws f hb).
split.
- move=> hAC T hTA hT.
  have he : A `&` T=T.
    apply/seteqP; split; first by move=> x [_ hx].
    move=> x hx; split=> //; exact: hTA x hx.
  have hz := hAC T hT; rewrite /measure_restrict he in hz.
  apply/eqP; rewrite eq_le (measure_nonnegative hb _) andbT -hz.
  exact: (@mapping_image_cost_below_caratheodory R X Y f beta hb T).
- move=> hImage N hN.
  have [B [hNB [hB hmass]]] := borel_regular_cover hrl N.
  have hBN : lambda B=0 by rewrite -hmass.
  have hsub : A `&` B `<=` A by move=> x [].
  have hzero : lambda (A `&` B)=0.
    apply: (@measure_null_subset R X lambda hl _ B _ hBN); by move=> x [].
  have himage := hImage (A `&` B) hsub hzero.
  have hz := @borel_null_image_caratheodory_null R X Y f beta D (A `&` B)
    hb hD hden (@borel_family_binary_intersection X setT _ (borel_sets_family X) A B hA hB) himage.
  apply: (@measure_null_subset R X mu hm _ (A `&` B) _ hz).
  by move=> x [hxA hxN]; split=> //; exact: hNB x hxN.
Qed.

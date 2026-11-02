(** Private existence proof for Federer (1969), 2.6.1, pp. 114–115 The
    locally proved fixed-family covering theorem supplies the measure laws.
    Nonmeasurable pairs are assigned infinite cost internally; this cannot
    reduce the infimum over admissible measurable rectangles. Downstream
    modules use only the sealed abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport
  CountableCoverEnvelopeUP CountableCoverEnvelopeSealed CountableCoverEnvelopeLaws CountableCoverEnvelopeBasic
  ProductMeasureUP ProductMeasureCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_rectangle_cover_cost]: private encoding
    of admissible rectangles for Federer 2.6.1, pp. 114–115.
    An inadmissible pair has infinite cost, so it contributes no
    smaller covering bound. On admissible pairs the cost is exactly
    alpha(A) beta(B), including the zero-times-infinity convention. *)
Definition product_rectangle_cover_cost (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (p : set X * set Y) :=
  if pselect (measure_measurable alpha p.1 /\ measure_measurable beta p.2)
  then alpha p.1 * beta p.2 else +oo.

(** Source for [product_measure_exists]: existence of the Cartesian product
    with both its defining infimum and largest- measure laws in Federer
    2.6.1, pp. 114–115 No finite-measure or countable-measurability
    assumption is imposed on either factor. *)
Theorem product_measure_exists (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) :
  is_measure alpha -> is_measure beta -> exists nu,
    is_product_measure alpha beta nu /\ is_product_cover_infimum alpha beta nu.
Proof.
move=> ha hb.
pose J := [the choiceType of (set X * set Y)%type].
pose S (p : J) := p.1 `*` p.2.
pose cost := product_rectangle_cover_cost alpha beta.
pose nu := @CountableCoverEnvelope.value R (X * Y)%type J S cost.
have hnu := @CountableCoverEnvelope.laws R (X * Y)%type J S cost.
have hcost p : 0 <= cost p.
  rewrite /cost /product_rectangle_cover_cost; case: pselect=> h; last exact: leey.
  exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have hc p : measure_measurable alpha p.1 /\ measure_measurable beta p.2 ->
    cost p=alpha p.1 * beta p.2.
  move=> hp; rewrite /cost /product_rectangle_cover_cost; by case: pselect.
have hm : is_measure nu := countable_cover_envelope_is_measure hnu hcost.
have hrect A B : measure_measurable alpha A -> measure_measurable beta B ->
    nu (A `*` B) <= alpha A * beta B.
  move=> hA hB; have hh := countable_cover_envelope_generator_bound hnu (hcost (A,B)).
  by rewrite (hc (A,B) (conj hA hB)) in hh.
have hmax eta : is_measure eta ->
    (forall A B, measure_measurable alpha A -> measure_measurable beta B ->
      eta (A `*` B) <= alpha A * beta B) -> forall E, eta E <= nu E.
  move=> he hr E; apply: (countable_cover_envelope_greatest hnu)=> G hG hcover.
  apply: le_trans (@measure_indexed_cover R (X * Y)%type J eta he E G S hG hcover) _.
  apply: nonnegative_sum_mono=> p hp.
  rewrite /cost /product_rectangle_cover_cost; case: pselect=> [[hA hB]|hn]; last exact: leey.
  exact: hr p.1 p.2 hA hB.
exists nu; split; first by constructor.
constructor.
- move=> E G hG hmeas hcover.
  have hh := @countable_cover_envelope_lower R (X * Y)%type J S cost nu hnu E G hG hcover.
  have he : nonnegative_sum G cost=nonnegative_sum G (fun p => alpha p.1 * beta p.2).
    apply: nonnegative_sum_ext=> p hp; exact: hc p (hmeas p hp).
  by rewrite -he.
- move=> E b hbound; apply: (countable_cover_envelope_greatest hnu)=> G hG hcover.
  case: (pselect (forall p, G p -> measure_measurable alpha p.1 /\ measure_measurable beta p.2))=> hg.
  + have he : nonnegative_sum G cost=nonnegative_sum G (fun p => alpha p.1 * beta p.2).
      apply: nonnegative_sum_ext=> p hp; exact: hc p (hg p hp).
    rewrite he; exact: hbound G hG hg hcover.
  + have [p [hp hbad]] : exists p, G p /\ ~ (measure_measurable alpha p.1 /\ measure_measurable beta p.2).
      apply: contrapT=> hn; apply: hg=> p hp; apply: contrapT=> hbad; apply: hn; exists p; by split.
    have he : cost p=+oo.
      rewrite /cost /product_rectangle_cover_cost; by case: pselect.
    have hh := @nonnegative_sum_term R J G cost p hp.
    rewrite he in hh; exact: le_trans (leey b) hh.
Qed.

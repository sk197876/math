(** Federer (1969), 3.2.46, p. 282: local area
    measures on injective chart pieces are evaluated on their
    actual images. These supporting outer-measure and Borel
    facts expand the localization procedure using 2.1.2,
    pp. 53–54, and 2.2.3, p. 61. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_image_pullback]: evaluation on
    the actual image under a chart, supporting 3.2.46,
    p. 282. This formula introduces no selected chart,
    auxiliary measure witness or assumed area identity. *)
Definition measure_image_pullback (R : realType) (X Y : choiceType)
    (f : X -> Y) (nu : set Y -> \bar R) (S : set X) := nu (f @` S).

(** Source for [measure_image_pullback_is_measure]: the
    countable covering inequality of 2.1.2, p. 53,
    for actual image costs, supporting 3.2.46, p. 282.
    Injectivity is unnecessary for the outer-measure laws. *)
Lemma measure_image_pullback_is_measure (R : realType) (X Y : choiceType)
    (f : X -> Y) (nu : set Y -> \bar R) :
  is_measure nu -> is_measure (measure_image_pullback f nu).
Proof.
move=> hNu; constructor; first by move=> S; exact (@measure_nonnegative R Y nu hNu (f @` S)).
move=> S F hF hCover.
apply: (@measure_indexed_cover R Y [the choiceType of set X] nu hNu
  (f @` S) F (fun B=>f @` B) hF).
move=> y [x hx <-]; have [B hB hxB] := hCover x hx.
exists B; first exact hB; by exists x.
Qed.

(** Source for [measure_image_pullback_measurable]: an
    injective chart transports measurability of an actual
    image to its source, supporting 3.2.46, p. 282.
    The proof uses exact intersections and differences,
    not a blanket claim about completed preimages. *)
Lemma measure_image_pullback_measurable (R : realType) (X Y : choiceType)
    (f : X -> Y) (nu : set Y -> \bar R) (B : set X) :
  injective f -> measure_measurable nu (f @` B) ->
  measure_measurable (measure_image_pullback f nu) B.
Proof.
move=> hInj hB T; rewrite /measure_image_pullback (hB (f @` T)).
have hIntersection : (f @` T) `&` (f @` B)=f @` (T `&` B).
  apply/seteqP; split=> y.
  - move=> [[x hx <-] [z hz hEq]]; exists x; last by [].
    split; first exact hx; have hzx : z=x := hInj _ _ hEq; by rewrite -hzx.
  - move=> [x [hx hBx] <-]; split; by exists x.
have hDifference : (f @` T) `\` (f @` B)=f @` (T `\` B).
  apply/seteqP; split=> y.
  - move=> [[x hx <-] hNot]; exists x; last by [].
    split; first exact hx; move=> hBx; apply: hNot; by exists x.
  - move=> [x [hx hNot] <-]; split; first by exists x.
    move=> [z hz hEq]; have hzx : z=x := hInj _ _ hEq.
    apply: hNot; by rewrite -hzx.
by rewrite hIntersection hDifference.
Qed.

(** Source for [measure_image_pullback_borel_regular]:
    an injective continuous chart whose Borel images are
    Borel induces a Borel regular image-cost measure,
    supporting 3.2.46, p. 282. Covers have equal
    outer mass; their excess over an arbitrary original
    subset is never asserted null. *)
Theorem measure_image_pullback_borel_regular (R : realType)
    (X Y : topologicalType) (f : X -> Y) (nu : set Y -> \bar R) :
  is_measure nu -> is_borel_regular_measure nu -> injective f -> continuous f ->
  (forall B, borel_set B -> borel_set (f @` B)) ->
  is_borel_regular_measure (measure_image_pullback f nu).
Proof.
move=> hNu hRegular hInj hCont hImages.
have hMu := measure_image_pullback_is_measure f hNu.
constructor.
- move=> U hU; apply: measure_image_pullback_measurable hInj _.
  exact (@borel_regular_borel_measurable R Y nu hNu hRegular
    (f @` U) (@hImages U (open_borel_set hU))).
- move=> S.
  have [W [hSW [hW hMass]]] := borel_regular_cover hRegular (f @` S).
  exists (f @^-1` W); split.
  + move=> x hx; apply: hSW; by exists x.
  + split; first exact (@continuous_borel_preimage X Y f hCont W hW).
    apply/eqP; rewrite eq_le; apply/andP; split.
    * apply: (@measure_mono R X (measure_image_pullback f nu) hMu).
      move=> x hx; apply: hSW; by exists x.
    * rewrite /measure_image_pullback hMass.
      apply: (@measure_mono R Y nu hNu).
      by move=> y [x hx <-].
Qed.

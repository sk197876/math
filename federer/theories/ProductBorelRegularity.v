(** Federer (1969), 2.6.5, p. 120: products of Lebesgue measures are Borel
    regular. Equal-measure Borel hulls follow by intersecting countably many
    near-optimal Borel rectangle covers. Open-set measurability uses
    countable bases, while the hull assertion itself does not. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic BorelRegularMeasureUP
  TopologicalBorel CountableOpenBaseUP ExtendedRealReciprocalBounds ProductMeasure
  ProductMeasureSequenceInfimum ProductBorelRectangles ProductBorelCoverApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_borel_hull]: Supporting Federer 2.6.5, p.
    120.The finite case intersects reciprocal-error covers as in the proof
    of 2.6.2, p. 116; the infinite case uses the whole space. *)
Theorem product_measure_borel_hull (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (hra : is_borel_regular_measure alpha) (hrb : is_borel_regular_measure beta)
    (S : set (X * Y)) :
  exists W, S `<=` W /\ borel_set W /\ product_measure ha hb S = product_measure ha hb W.
Proof.
pose nu := product_measure ha hb; have hm := product_measure_is_measure ha hb.
have hpos : 0 <= nu S := measure_nonnegative hm S.
case he: (nu S)=> [r| |]; last by rewrite he in hpos.
- have hex n : exists (A : nat -> set X) (B : nat -> set Y),
      (forall m, borel_set (A m) /\ borel_set (B m)) /\
      S `<=` (\bigcup_m (A m `*` B m)) /\
      nonnegative_sum setT (fun m => alpha (A m) * beta (B m)) < (r + ((n.+1)%:R)^-1)%:E.
    apply: (@product_measure_borel_cover_approximation R X Y alpha beta ha hb hra hrb S).
    change (nu S < (r + ((n.+1)%:R)^-1)%:E).
    by rewrite he lte_fin ltrDl invr_gt0 ltr0n.
  pose A n := projT1 (cid (hex n)).
  pose B n := projT1 (cid (projT2 (cid (hex n)))).
  have h n := projT2 (cid (projT2 (cid (hex n)))).
  pose W := \bigcap_n (\bigcup_m (A n m `*` B n m)).
  have hSW : S `<=` W by move=> p hp n _; exact: (h n).2.1 p hp.
  have hW : borel_set W.
    apply: borel_set_countable_intersection; first exact: countableP.
    - by exists 0%N.
    - move=> n _; apply: borel_set_countable_union; first exact: countableP.
      move=> m _; exact (borel_product_rectangle ((h n).1 m).1 ((h n).1 m).2).
  exists W; split=> //; split=> //.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + exact (@measure_mono R (X * Y)%type nu hm S W hSW).
  + change (nu W <= nu S); rewrite he; apply: extended_real_reciprocal_upper_bound=> n.
    have hc : W `<=` \bigcup_m (A n m `*` B n m) by move=> p hp; exact: hp n Logic.I.
    have hmeas m : measure_measurable alpha (A n m) /\ measure_measurable beta (B n m).
      split.
      - exact (@borel_regular_borel_measurable R X alpha ha hra (A n m) ((h n).1 m).1).
      - exact (@borel_regular_borel_measurable R Y beta hb hrb (B n m) ((h n).1 m).2).
    have hbound := @product_measure_sequence_cover_bound R X Y alpha beta ha hb W (A n) (B n) hmeas hc.
    exact: le_trans hbound (ltW (h n).2.2).
- exists setT; split; first by move=> p _.
  split; first exact: open_borel_set openT.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + apply: (measure_mono hm)=> p _; exact Logic.I.
  + change (nu setT <= nu S); rewrite he; exact: leey.
Qed.

(** Source for [product_measure_borel_regular]: Supporting Federer 2.6.5, p.
    120.Countable topological bases are assumed, but the measures need not
    be finite or countably measurable. *)
Theorem product_measure_borel_regular (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (U : nat -> set X) (V : nat -> set Y) :
  is_countable_open_base U -> is_countable_open_base V ->
  is_borel_regular_measure alpha -> is_borel_regular_measure beta ->
  is_borel_regular_measure (product_measure ha hb).
Proof.
move=> hU hV hra hrb; constructor.
- exact (@product_open_sets_measurable R X Y alpha beta ha hb U V hU hV
    (borel_regular_open_measurable hra) (borel_regular_open_measurable hrb)).
- exact (@product_measure_borel_hull R X Y alpha beta ha hb hra hrb).
Qed.

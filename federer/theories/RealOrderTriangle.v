(** Federer (1969), 2.6.7, printed p. 121: the triangle S = {(x,y) : a <= x
    < y <= b} and its two sections. Measurability is obtained from countably
    many measurable rectangles, as in the proof of 2.6.2, pp. 115–117. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  MeasureCountableClosure ProductMeasure ProductSections ProductRectangleMeasurability
  MeasurableRealPairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_order_triangle]: the set S used to prove
    Federer 2.6.7, p. 121. Endpoint inequalities are kept
    exactly as printed, so atoms at endpoints are allowed. *)
Definition real_order_triangle (R : realType) (a b : R) : set (R * R) :=
  [set p | a <= p.1 /\ p.1 < p.2 /\ p.2 <= b].

(** Source for [real_order_triangle_horizontal]: horizontal
    section [a,y) of S for a < y <= b, and the empty
    section otherwise, Federer 2.6.7, p. 121, first equation. *)
Lemma real_order_triangle_horizontal (R : realType) (a b y : R) :
  product_horizontal_section (real_order_triangle a b) y =
    if (a < y) && (y <= b) then [set x | a <= x /\ x < y] else set0.
Proof.
case: ifP=> [/andP [hay hyb]|hy].
- apply/seteqP; split=> x; first by move=> [hax [hxy _]].
  by move=> [hax hxy]; split=> //; split.
- apply/seteqP; split; last by move=> x [].
  move=> x [hax [hxy hyb]].
  have hay := le_lt_trans hax hxy; by move: hy; rewrite hay hyb.
Qed.

(** Source for [real_order_triangle_vertical]: vertical section
    (x,b] of S for a <= x < b, and the empty section
    otherwise, Federer 2.6.7, p. 121, second equation. *)
Lemma real_order_triangle_vertical (R : realType) (a b x : R) :
  product_vertical_section (real_order_triangle a b) x =
    if (a <= x) && (x < b) then [set y | x < y /\ y <= b] else set0.
Proof.
case: ifP=> [/andP [hax hxb]|hx].
- apply/seteqP; split=> y; first by move=> [_ hy].
  by move=> [hxy hyb]; split=> //; split.
- apply/seteqP; split; last by move=> y [].
  move=> y [hax [hxy hyb]].
  have hxb := lt_le_trans hxy hyb; by move: hx; rewrite hax hxb.
Qed.

(** Source for [real_order_triangle_rectangle_bound]: S is
    contained in [a,b) times (a,b], supporting the finite
    product-measure hypothesis for Fubini in Federer 2.6.7, p. 121. *)
Lemma real_order_triangle_rectangle_bound (R : realType) (a b : R) :
  real_order_triangle a b `<=`
    [set x | a <= x /\ x < b] `*` [set y | a < y /\ y <= b].
Proof.
move=> [x y] [hax [hxy hyb]]; split; split=> //.
- exact: lt_le_trans hxy hyb.
- exact: le_lt_trans hax hxy.
Qed.

(** Source for [lower_open_rays_left_interval]: measurable
    half-open intervals [a,b), supporting Federer 2.6.7,
    p. 121, by complements and intersections from 2.1.3(2), p. 55. *)
Lemma lower_open_rays_left_interval (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu) :
  (forall t, measure_measurable mu [set x | x < t]) ->
  forall a b, measure_measurable mu [set x | a <= x /\ x < b].
Proof.
move=> hr a b.
have he : [set x | a <= x /\ x < b]=[set x | x < b] `\` [set x | x < a].
  apply/seteqP; split=> x.
  - move=> [hax hxb]; split=> //; apply/negP; by rewrite -leNgt.
  - move=> [hxb /negP hxa]; split=> //; by rewrite leNgt.
rewrite he; exact (@measure_measurable_difference R R mu hm _ _ (hr b) (hr a)).
Qed.

(** Source for [lower_closed_rays_right_interval]: measurable
    half-open intervals (a,b], supporting Federer 2.6.7,
    p. 121, with its opposite endpoint convention. *)
Lemma lower_closed_rays_right_interval (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu) :
  (forall t, measure_measurable mu [set x | x <= t]) ->
  forall a b, measure_measurable mu [set x | a < x /\ x <= b].
Proof.
move=> hr a b.
have he : [set x | a < x /\ x <= b]=[set x | x <= b] `\` [set x | x <= a].
  apply/seteqP; split=> x.
  - move=> [hax hxb]; split=> //; apply/negP; by rewrite -ltNge.
  - move=> [hxb /negP hxa]; split=> //; by rewrite ltNge.
rewrite he; exact (@measure_measurable_difference R R mu hm _ _ (hr b) (hr a)).
Qed.

(** Source for [real_order_triangle_measurable]: measurable S
    in the application of 2.6.2(3) on p. 121 of Federer
    2.6.7. Rational cuts express x < y as a countable
    union of measurable rectangles; no product topology or
    external product-measure implementation is imported. *)
Theorem real_order_triangle_measurable (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (a b : R) :
  (forall t, measure_measurable alpha [set x | x < t]) ->
  (forall t, measure_measurable beta [set x | x <= t]) ->
  measure_measurable (product_measure ha hb) (real_order_triangle a b).
Proof.
move=> hAr hBr.
pose A := [set x : R | a <= x /\ x < b].
pose B := [set y : R | a < y /\ y <= b].
pose C (q : rat) := (A `&` [set x | x < ratr q]) `*` (B `&` [set y | ratr q < y]).
have he : real_order_triangle a b=\bigcup_(q in @setT rat) C q.
  apply/seteqP; split=> [[x y] hs|[x y] [q _ [[hx hxq] [hy hqy]]]].
  - have [q [hxq hqy]] := @real_rationals_order_dense R x y hs.2.1.
    exists q=> //; have [hx hy] := real_order_triangle_rectangle_bound hs.
    by split; split.
  - split; first exact hx.1.
    split; [exact: lt_trans hxq hqy|exact hy.2].
rewrite he; apply: (measure_measurable_countable_union (product_measure_is_measure ha hb)); first exact: countableP.
move=> q _; apply: (product_measure_rectangle_measurable ha hb).
- exact (@measure_measurable_intersection R R alpha ha A _
    (@lower_open_rays_left_interval R alpha ha hAr a b) (hAr (ratr q))).
- have hU : [set y : R | ratr q < y]=~` [set y : R | y <= ratr q].
    apply/seteqP; split=> y /=.
    + move=> hqy; apply/negP; by rewrite -ltNge.
    + move=> /negP hy; by rewrite ltNge.
  apply: (@measure_measurable_intersection R R beta hb B _).
  + exact (@lower_closed_rays_right_interval R beta hb hBr a b).
  + rewrite hU; exact: measure_measurable_complement (hBr (ratr q)).
Qed.

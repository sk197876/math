(** Federer (1969), 2.6.2, pp. 115–116: apply nonnegative countable
    integration twice to a disjoint family of rectangles. The specification
    of the disjoint family is used directly; no particular refinement
    construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureCountableClosure MeasureCountableAdditivity
  MeasureIntegralUP MeasureIntegralGraphEquivalence NonnegativeSum NonnegativeSumSupport
  ProductMeasure ProductRectangleMeasurability ProductRectangleValue ProductSections
  DisjointRectangleCoverUP RectangleSectionIntegral TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_rectangle_cover_vertical_measurable]:
    section measurability for the disjoint-rectangle representation
    used in Federer 2.6.2, p. 116. All sections
    are measurable in this case, before null modifications are allowed. *)
Lemma disjoint_rectangle_cover_vertical_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (hb : is_measure beta) (G : set (set X * set Y)) (S : set (X * Y)) :
  countable G -> is_disjoint_rectangle_cover alpha beta G S ->
  forall x, measure_measurable beta (product_vertical_section S x).
Proof.
move=> hc hg x; rewrite (disjoint_rectangle_union hg) product_vertical_union.
apply: (@measure_measurable_countable_union R Y [the choiceType of (set X * set Y)%type]
  beta hb G _ hc)=> p hp.
exact (@rectangle_vertical_section_measurable R X Y beta hb p.1 p.2 (disjoint_rectangle_factors hg hp).2 x).
Qed.

(** Source for [disjoint_rectangle_cover_vertical_integral]: direct
    repeated-integral equality for a countable disjoint rectangle family in
    Federer 2.6.2, pp. 115–116 Infinite product measure and an empty
    covering family are both permitted. *)
Lemma disjoint_rectangle_cover_vertical_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (G : set (set X * set Y)) (S : set (X * Y)) :
  countable G -> is_disjoint_rectangle_cover alpha beta G S ->
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x)))
    (product_measure ha hb S).
Proof.
move=> hc hg.
pose rect (p : set X * set Y) := p.1 `*` p.2.
pose u (p : set X * set Y) x : extended_real_line R := beta (product_vertical_section (rect p) x).
pose a (p : set X * set Y) := alpha p.1*beta p.2.
have hu p : G p -> forall x, 0 <= u p x by move=> _ x; exact: measure_nonnegative.
have hi p (hp : G p) : is_measure_integral alpha (partial_function_total (u p)) (a p).
  exact (@rectangle_vertical_section_integral R X Y alpha beta ha hb p.1 p.2
    (disjoint_rectangle_factors hg hp).1 (disjoint_rectangle_factors hg hp).2).
have hsum := @total_countable_nonnegative_integral R X [the choiceType of (set X * set Y)%type]
  alpha ha G u a hc hu hi.
have hpoint x : beta (product_vertical_section S x) = nonnegative_sum G (fun p => u p x).
  rewrite (disjoint_rectangle_union hg) product_vertical_union.
  apply: (@measure_countable_disjoint_additivity R Y [the choiceType of (set X * set Y)%type] beta hb G _ hc).
  - move=> p hp; exact (@rectangle_vertical_section_measurable R X Y beta hb p.1 p.2
      (disjoint_rectangle_factors hg hp).2 x).
  - move=> p q hp hq hne y hpy hqy.
    apply: (@disjoint_rectangle_pieces R X Y alpha beta G S hg p q hp hq _ (x,y) hpy hqy).
    by move=> he; move: hne; rewrite he eqxx.
have hvalue : product_measure ha hb S = nonnegative_sum G a.
  rewrite (disjoint_rectangle_union hg).
  have he := @measure_countable_disjoint_additivity R (X * Y)%type [the choiceType of (set X * set Y)%type]
    (product_measure ha hb) (product_measure_is_measure ha hb) G rect hc.
  have hm p (hp : G p) : measure_measurable (product_measure ha hb) (rect p).
    exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb p.1 p.2
      (disjoint_rectangle_factors hg hp).1 (disjoint_rectangle_factors hg hp).2).
  have hd p q (hp : G p) (hq : G q) (hne : p != q) : forall z, rect p z -> rect q z -> False.
    apply: (@disjoint_rectangle_pieces R X Y alpha beta G S hg p q hp hq).
    by move=> e; move: hne; rewrite e eqxx.
  rewrite (he hm hd); apply: nonnegative_sum_ext=> p hp.
  exact (@product_measure_rectangle_value R X Y alpha beta ha hb p.1 p.2
    (disjoint_rectangle_factors hg hp).1 (disjoint_rectangle_factors hg hp).2).
rewrite hvalue; apply: (@measure_integral_graph_equivalent R X alpha _ _ _ _ hsum)=> x y.
by change (nonnegative_sum G (fun p => u p x) = y <-> beta (product_vertical_section S x) = y); rewrite hpoint.
Qed.

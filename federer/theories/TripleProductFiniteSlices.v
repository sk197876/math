(** Corrected associativity for Federer (1969), 2.6.5, p. 119. The
    intermediate argument here fixes a measurable finite-mass outer factor
    and applies the largest-measure property of 2.6.1, p. 115, to the
    remaining pair. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasurePushforward
  ProductMeasure ProductRectangleMeasurability ProductRectangleValue FiniteMeasureScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [left_triple_slice_measure]: supporting restriction and image
    measure from Federer 2.1.2, p. 54, for the corrected associativity of
    2.6.5, p. 119 *)
Definition left_triple_slice_measure (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma) (A : set X) :=
  measure_pushforward (fun p : (X * Y) * Z => (p.1.2,p.2))
    (measure_restrict (product_measure (product_measure_is_measure ha hb) hg)
      [set p | A p.1.1]).

(** Source for [left_triple_slice_is_measure]: supporting restriction and
    image laws from Federer 2.1.2, p. 54, used in corrected 2.6.5, p. 119 (. *)
Lemma left_triple_slice_is_measure (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma) (A : set X) :
  is_measure (left_triple_slice_measure ha hb hg A).
Proof.
apply: measure_pushforward_is_measure; apply: measure_restrict_is_measure.
exact: product_measure_is_measure.
Qed.

(** Source for [left_triple_slice_rectangle]: exact three-factor rectangle
    value from two applications of Federer 2.6.2(2), p. 115; supports
    corrected 2.6.5, p. 119 (. No finiteness is required. *)
Lemma left_triple_slice_rectangle (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma)
    (A : set X) (B : set Y) (C : set Z) :
  measure_measurable alpha A -> measure_measurable beta B -> measure_measurable gamma C ->
  left_triple_slice_measure ha hb hg A (B `*` C) = alpha A * (beta B * gamma C).
Proof.
move=> hA hB hC.
have he : [set p : (X * Y) * Z | A p.1.1] `&`
    ((fun p : (X * Y) * Z => (p.1.2,p.2)) @^-1` (B `*` C)) = (A `*` B) `*` C.
  apply/seteqP; split; move=> [[x y] z] /=.
  - by move=> [hx [hy hz]]; split; first split.
  - by move=> [[hx hy] hz]; split=> //; split.
rewrite /left_triple_slice_measure /measure_pushforward /measure_restrict he.
rewrite (product_measure_rectangle_value (product_measure_is_measure ha hb) hg
  (product_measure_rectangle_measurable ha hb hA hB) hC).
by rewrite (product_measure_rectangle_value ha hb hA hB) muleA.
Qed.

(** Source for [left_triple_finite_slice_bound]: supporting
    finite-outer-factor bound for corrected Federer 2.6.5, p. 119. Divide
    the slice measure by its finite positive alpha mass, use 2.6.1's
    extremal property, and treat zero mass separately. *)
Lemma left_triple_finite_slice_bound (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma)
    (A : set X) (E : set (Y * Z)) :
  measure_measurable alpha A -> alpha A < +oo ->
  left_triple_slice_measure ha hb hg A E <= alpha A * product_measure hb hg E.
Proof.
move=> hA hf.
have hfin : alpha A \is a fin_num by rewrite ge0_fin_numE //; exact (measure_nonnegative ha _).
have hc : (0 <= fine (alpha A))%R by apply: fine_ge0; exact (measure_nonnegative ha _).
rewrite -(fineK hfin).
apply: (@nonnegative_finite_factor_product_domination R Y Z beta gamma hb hg
  (left_triple_slice_measure ha hb hg A) (left_triple_slice_is_measure ha hb hg A) (fine (alpha A)) hc).
move=> B C hB hC; rewrite fineK // (left_triple_slice_rectangle ha hb hg hA hB hC).
exact: lexx.
Qed.

(** Source for [right_triple_slice_measure]: symmetric supporting
    restriction to a fixed third factor for corrected Federer 2.6.5, p. 119
    (. *)
Definition right_triple_slice_measure (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma) (C : set Z) :=
  measure_pushforward (fun p : X * (Y * Z) => (p.1,p.2.1))
    (measure_restrict (product_measure ha (product_measure_is_measure hb hg))
      [set p | C p.2.2]).

(** Source for [right_triple_slice_is_measure]: supporting restriction and
    image laws from Federer 2.1.2, p. 54, for corrected 2.6.5, p. 119 (. *)
Lemma right_triple_slice_is_measure (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma) (C : set Z) :
  is_measure (right_triple_slice_measure ha hb hg C).
Proof.
apply: measure_pushforward_is_measure; apply: measure_restrict_is_measure.
exact: product_measure_is_measure.
Qed.

(** Source for [right_triple_slice_rectangle]: two applications of Federer
    2.6.2(2), p. 115, for the other association; supports corrected 2.6.5,
    p. 119 (. *)
Lemma right_triple_slice_rectangle (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma)
    (A : set X) (B : set Y) (C : set Z) :
  measure_measurable alpha A -> measure_measurable beta B -> measure_measurable gamma C ->
  right_triple_slice_measure ha hb hg C (A `*` B) = gamma C * (alpha A * beta B).
Proof.
move=> hA hB hC.
have he : [set p : X * (Y * Z) | C p.2.2] `&`
    ((fun p : X * (Y * Z) => (p.1,p.2.1)) @^-1` (A `*` B)) = A `*` (B `*` C).
  apply/seteqP; split; move=> [x [y z]] /=.
  - by move=> [hz [hx hy]]; split=> //; split.
  - by move=> [hx [hy hz]]; split=> //; split.
rewrite /right_triple_slice_measure /measure_pushforward /measure_restrict he.
rewrite (product_measure_rectangle_value ha (product_measure_is_measure hb hg)
  hA (product_measure_rectangle_measurable hb hg hB hC)).
by rewrite (product_measure_rectangle_value hb hg hB hC) muleA [gamma C * _]muleC.
Qed.

(** Source for [right_triple_finite_slice_bound]: supporting
    finite-third-factor bound in corrected Federer 2.6.5, p. 119; the
    symmetric instance of the extremal measure argument. *)
Lemma right_triple_finite_slice_bound (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hg : is_measure gamma)
    (C : set Z) (E : set (X * Y)) :
  measure_measurable gamma C -> gamma C < +oo ->
  right_triple_slice_measure ha hb hg C E <= gamma C * product_measure ha hb E.
Proof.
move=> hC hf.
have hfin : gamma C \is a fin_num by rewrite ge0_fin_numE //; exact (measure_nonnegative hg _).
have hc : (0 <= fine (gamma C))%R by apply: fine_ge0; exact (measure_nonnegative hg _).
rewrite -(fineK hfin).
apply: (@nonnegative_finite_factor_product_domination R X Y alpha beta ha hb
  (right_triple_slice_measure ha hb hg C) (right_triple_slice_is_measure ha hb hg C) (fine (gamma C)) hc).
move=> A B hA hB; rewrite fineK // (right_triple_slice_rectangle ha hb hg hA hB hC).
exact: lexx.
Qed.

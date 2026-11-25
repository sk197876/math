(** Federer (1969), 2.1.5, p. 57, failure of (5) for the corrected third
    irregular measure. Federer's erratum p. 1, book p. 57 line 26, replaces
    card(S) by card(A). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSumSupport CountingMeasure MeasureUP
  MeasureRestriction TwoPointRestrictionMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [two_point_restriction_contains_outside]: Federer
    2.1.5, p. 57, supporting evaluation of a set containing the
    third point, hence not contained in S. Its measure is two. *)
Lemma two_point_restriction_contains_outside (R : realType) (A : set (option bool)) :
  A None -> two_point_restriction_measure (R := R) A = (2 : R)%:E.
Proof. by move=> h; rewrite /two_point_restriction_measure (mem_set h). Qed.

(** Source for [two_point_restriction_singleton_inside]: Federer
    2.1.5, p. 57, corrected singleton value one inside S; erratum
    p. 1, book p. 57 line 26. *)
Lemma two_point_restriction_singleton_inside (R : realType) (b : bool) :
  two_point_restriction_measure (R := R) [set Some b] = (1 : R)%:E.
Proof.
rewrite (@two_point_restriction_measure_inside R [set Some b]); last by move=> x ->.
by rewrite counting_measure_sum nonnegative_sum_singleton // lee_fin ler01.
Qed.

(** Source for [two_point_restriction_agrees_with_counting]: Federer
    2.1.5, p. 57, supporting verification that restriction to S
    is counting measure restricted to S, using the corrected formula. *)
Lemma two_point_restriction_agrees_with_counting (R : realType) :
  measure_restrict (@two_point_restriction_measure R) two_point_support =
  measure_restrict (@counting_measure R _) two_point_support.
Proof.
apply: funext=> A; rewrite /measure_restrict.
apply: two_point_restriction_measure_inside=> x [hx _]; exact hx.
Qed.

(** Source for [two_point_restriction_all_measurable]: Federer
    2.1.5, p. 57, supporting measurability of every subset for the
    restricted measure in the third counterexample. *)
Lemma two_point_restriction_all_measurable (R : realType) (A : set (option bool)) :
  measure_measurable (measure_restrict (@two_point_restriction_measure R) two_point_support) A.
Proof.
rewrite two_point_restriction_agrees_with_counting.
exact: (@measure_restrict_measurable R _ (@counting_measure R _) two_point_support A
  (@counting_measure_measurable R _ A)).
Qed.

(** Source for [two_point_restriction_measurable_no_separation]:
    Federer 2.1.5, p. 57, supporting obstruction to the representation
    in (5). No originally measurable set can contain Some false while
    excluding Some true; a test with the third point violates splitting. *)
Lemma two_point_restriction_measurable_no_separation (R : realType)
    (A : set (option bool)) :
  measure_measurable (@two_point_restriction_measure R) A ->
  A (Some false) -> A (Some true).
Proof.
move=> hA ha; case: (pselect (A (Some true)))=> hb; first exact hb.
exfalso; case: (pselect (A None))=> hc.
- pose T : set (option bool) := [set None] `|` [set Some true].
  have hT : T None by left.
  have hI : (T `&` A) None by split.
  have hd : T `\` A = [set Some true].
    apply/seteqP; split.
    + move=> x [[->|->] hn] //; exfalso; exact: hn hc.
    + move=> x ->; split.
      * by right.
      * exact hb.
  have he := hA T; rewrite hd (@two_point_restriction_contains_outside R T hT)
    (@two_point_restriction_contains_outside R (T `&` A) hI)
    two_point_restriction_singleton_inside in he.
  have hlt : (2 : R)%:E < (2 : R)%:E + (1 : R)%:E by rewrite -EFinD lte_fin ltrDl ltr01.
  by rewrite -he ltxx in hlt.
- pose T : set (option bool) := [set None] `|` [set Some false].
  have hT : T None by left.
  have hD : (T `\` A) None by split.
  have hi : T `&` A = [set Some false].
    apply/seteqP; split.
    + move=> x [[->|->] hx] //; exfalso; exact: hc hx.
    + move=> x ->; split.
      * by right.
      * exact ha.
  have he := hA T; rewrite hi (@two_point_restriction_contains_outside R T hT)
    (@two_point_restriction_contains_outside R (T `\` A) hD)
    two_point_restriction_singleton_inside in he.
  have hlt : (2 : R)%:E < (1 : R)%:E + (2 : R)%:E by rewrite -EFinD lte_fin ltrDr ltr01.
  by rewrite -he ltxx in hlt.
Qed.

(** Source for [two_point_restriction_classification_counterexample]:
    Federer 2.1.5, p. 57, failure of (5) despite finite phi(S).
    The inside singleton is restricted-measurable but cannot be
    (B intersection S) union C with B originally measurable and C
    outside S. The corrected card(A) value is essential. *)
Theorem two_point_restriction_classification_counterexample (R : realType) :
  two_point_restriction_measure (R := R) two_point_support < +oo /\
  measure_measurable (measure_restrict (@two_point_restriction_measure R) two_point_support) [set Some false] /\
  ~ exists B C : set (option bool),
    measure_measurable (@two_point_restriction_measure R) B /\
    C `<=` ~` two_point_support /\ [set Some false] = (B `&` two_point_support) `|` C.
Proof.
split.
- rewrite two_point_restriction_measure_inside; last by move=> x hx.
  by rewrite two_point_support_counting ltry.
- split; first exact: two_point_restriction_all_measurable.
  move=> [B [C [hB [hC he]]]].
  have ha : ((B `&` two_point_support) `|` C) (Some false) by rewrite -he.
  have hBa : B (Some false).
    case: ha=> [[hb _]|hc] //.
    exfalso; apply: (hC (Some false) hc); by [].
  have hBb := @two_point_restriction_measurable_no_separation R B hB hBa.
  have hb : ((B `&` two_point_support) `|` C) (Some true) by left; split.
  rewrite -he in hb; discriminate hb.
Qed.

(** Supporting Federer (1969), 2.10.47(1), pp. 204–205: split a covering
    content across a coarse cube, after restricting to the set whose
    hyperplane boundaries are null. The argument is the printed regrouping
    of a cover by coarse cells, expressed through Caratheodory
    measurability. No measurability of all open or closed sets for gamma_i
    is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import CountableCoverEnvelopeUP CountableCoverEnvelopeBasic CountableCoverEnvelopeLaws
  RefiningCoverContent MeasureUP MeasureBasic MeasureRestriction MeasureSplit MeasureIndexedCover
  NonnegativeSum NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_cover_generator_split_measurable]:
    supporting restricted splitting criterion in 2.10.47(1),
    pp. 204–205. The generator cost pays for both pieces
    after restriction to D. This proves measurability for
    the restricted content; it does not assume it. *)
Theorem restricted_cover_generator_split_measurable (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (gamma : set X -> \bar R)
    (D A : set X) :
  is_countable_cover_envelope S cost gamma -> (forall j, 0<=cost j) ->
  (forall j, gamma ((D `&` S j) `&` A)+gamma ((D `&` S j) `\` A)<=cost j) ->
  measure_measurable (measure_restrict gamma D) A.
Proof.
move=> hg hc hsplit.
pose hm := countable_cover_envelope_is_measure hg hc.
pose hr := measure_restrict_is_measure hm D.
move=> T; apply/eqP; rewrite eq_le (measure_split_upper hr) /=.
change (gamma (D `&` (T `&` A))+gamma (D `&` (T `\` A))<=gamma (D `&` T)).
apply: (countable_cover_envelope_greatest hg)=> G hG hcov.
have hi : gamma (D `&` (T `&` A))<=nonnegative_sum G (fun j=>gamma ((D `&` S j) `&` A)).
  apply: (@measure_indexed_cover R X J gamma hm _ G _ hG)=> x [hxD [hxT hxA]].
  have [j hj hxj] := hcov x (conj hxD hxT).
  exists j=> //; by split; [split | ].
have hd : gamma (D `&` (T `\` A))<=nonnegative_sum G (fun j=>gamma ((D `&` S j) `\` A)).
  apply: (@measure_indexed_cover R X J gamma hm _ G _ hG)=> x [hxD [hxT hxA]].
  have [j hj hxj] := hcov x (conj hxD hxT).
  exists j=> //; by split; [split | ].
apply: le_trans (leeD hi hd) _.
rewrite -(@nonnegative_sum_add R J G (fun j=>gamma ((D `&` S j) `&` A))
  (fun j=>gamma ((D `&` S j) `\` A))
  (fun j _=>measure_nonnegative hm _) (fun j _=>measure_nonnegative hm _)).
apply: nonnegative_sum_mono=> j _; exact: hsplit.
Qed.

(** Source for [refining_content_cell_measurable_on]: supporting
    coarse-cell measurability in 2.10.47(1), pp. 204–205.
    Every finer cube lies in the coarse cell or meets it
    only in a null part of D. The Euclidean dyadic geometry
    and hyperplane-null reduction supply these premises later. *)
Theorem refining_content_cell_measurable_on (R : realType) (X : choiceType)
    H cost i gamma (D A : set X) :
  @is_refining_cover_content R X H cost i gamma ->
  (forall T, refining_cover_tail H i T -> 0<=cost T) ->
  (forall T, refining_cover_tail H i T ->
    (D `&` T) `<=` A \/ gamma ((D `&` T) `&` A)=0) ->
  measure_measurable (measure_restrict gamma D) A.
Proof.
move=> hg hc hcell.
pose hm := refining_cover_content_measure hg hc.
apply: (@restricted_cover_generator_split_measurable R X
  (set_type (refining_cover_tail H i)) (fun S=>val S) (fun S=>cost (val S)) gamma D A hg
  (fun S=>hc _ (set_valP S)))=> S.
have hgen := @refining_cover_content_generator R X H cost i gamma (val S) hg (set_valP S) (hc _ (set_valP S)).
case: (hcell (val S) (set_valP S))=> [hsub|hnull].
- have he : (D `&` val S) `\` A=set0.
    apply/seteqP; split=> [x [hx hn]|x []]; exact: hn (hsub x hx).
  rewrite he (measure_empty hm) adde0; apply: le_trans _ hgen.
  apply: (@measure_mono R X gamma hm)=> x hx; exact hx.1.2.
- rewrite hnull add0e; apply: le_trans _ hgen.
  apply: (@measure_mono R X gamma hm)=> x hx; exact hx.1.2.
Qed.

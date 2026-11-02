(** Supporting multiplicity facts for Federer (1969), 2.10.9–10, pp.
    175–176, and the extension of the geometric functional in 2.5.10, p.
    101, from Borel sets to finite H^1 measurable sets. The count is the
    actual counting measure of 2.1.2, p. 54. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic CountingMeasure CountingInjectionBound
  MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_zero_iff]: supporting
    zero-count criterion for N(f|A,y), Federer 2.10.9,
    p. 175: no inverse image point is present. *)
Lemma mapping_multiplicity_zero_iff (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (A : set X) y :
  @mapping_multiplicity R X Y p A y=0 <-> ~ (p @` A) y.
Proof.
split.
- move=> hz [x hx he].
  have hb : @counting_measure R X [set x]<=counting_measure (mapping_fibre p A y).
    apply: (@measure_mono R X _ (counting_measure_is_measure R X))=> z ->; by split.
  rewrite counting_measure_singleton_value -/(@mapping_multiplicity R X Y p A y) hz in hb.
  by move: hb; rewrite leNgt lte01.
- move=> hn; have he : mapping_fibre p A y=set0.
    apply/seteqP; split=> x; last by [].
    move=> [hx hpx]; exfalso; apply: hn; by exists x.
  rewrite /mapping_multiplicity he; exact: measure_empty (counting_measure_is_measure R X).
Qed.

(** Source for [mapping_fibre_sandwich_equal]: supporting
    null modification of the fibres in Federer 2.5.10,
    p. 101, using the Borel sandwich 2.2.3, p. 61.
    Outside the image of the excess B minus D, the
    intermediate set A has exactly the same fibre as D. *)
Lemma mapping_fibre_sandwich_equal (X : choiceType) (Y : Type)
    (p : X -> Y) (D A B : set X) y :
  D `<=` A -> A `<=` B -> ~ (p @` (B `\` D)) y ->
  mapping_fibre p D y=mapping_fibre p A y.
Proof.
move=> hDA hAB hn; apply/seteqP; split=> x [hx he]; split=> //.
- exact: hDA.
- apply: contrapT=> hDx; apply: hn; exists x=> //; split=> //; exact: hAB.
Qed.

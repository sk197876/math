(** Supporting the projection slicing formula in Federer (1969), 2.10.16, p.
    178. On each small source cell, count the q-fibre in its f-image. The
    sum lies between the number of source cells meeting the composite fibre
    and its full counting measure. This supplies the limiting comparison
    without assuming f injective. It expands the partition argument of
    2.10.10, p. 176, using 2.1.1–2.1.3, pp. 51–55. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport CountingMeasure
  CountingInjectionBound CountingImageBound MappingMultiplicity
  PartitionHitCounts PartitionImageCharacteristicSum
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ShrinkingBorelPartitionLevels
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureBasic
  MeasureDisjointSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [composite_fibre_image]: supporting set identity
    for 2.10.16, p. 178: the q-fibre in f(S) is the
    f-image of the composite fibre in S. This is elementary
    set theory, not an additional theorem attributed to Federer. *)
Lemma composite_fibre_image (X Y Z : Type) (f : X -> Y) (q : Y -> Z) S z :
  mapping_fibre q (f @` S) z=f @` mapping_fibre (fun x => q (f x)) S z.
Proof.
apply/seteqP; split=> y.
- move=> [[x hx <-] he]; exists x=> //; by split.
- move=> [x [hx he] <-]; split=> //; by exists x.
Qed.

(** Source for [partition_composed_multiplicity_sandwich]:
    supporting counting bounds for the last formula of
    2.10.16, p. 178. Distinct cells are disjoint, and
    projecting a cell can decrease its fibre count. Neither
    the source fibre nor its image is assumed countable. *)
Theorem partition_composed_multiplicity_sandwich (R : realType)
    (X Y Z : choiceType) (f : X -> Y) (q : Y -> Z)
    (E P : seq nat -> set X) (hP : is_cover_partition_tree E P) A j z :
  @partition_hit_count R X P (mapping_fibre (fun x => q (f x)) A z) j<=
    nonnegative_sum [set s | size s=j]
      (fun s => @mapping_multiplicity R Y Z q (f @` (A `&` P s)) z) /\
  nonnegative_sum [set s | size s=j]
      (fun s => @mapping_multiplicity R Y Z q (f @` (A `&` P s)) z)<=
    @mapping_multiplicity R X Z (fun x => q (f x)) A z.
Proof.
pose F := fun x => q (f x).
split.
- rewrite -(@partition_image_characteristic_sum R X Z F A P j z).
  apply: nonnegative_sum_mono=> s hs.
  have hc := @CharacteristicFunction.laws R Z (F @` (A `&` P s)).
  case: (pselect ((F @` (A `&` P s)) z))=> hz.
  + rewrite (characteristic_on_set hc hz).
    have [x [hx hxs] he] := hz.
    have hsub : [set f x] `<=` mapping_fibre q (f @` (A `&` P s)) z.
      move=> y ->; split; first by exists x=> //; split.
      exact he.
    rewrite -(@counting_measure_singleton_value R Y (f x)).
    exact (@measure_mono R Y _ (counting_measure_is_measure R Y) _ _ hsub).
  + rewrite (characteristic_off_set hc hz); exact: mapping_multiplicity_nonnegative.
- apply: le_trans (_ : nonnegative_sum [set s | size s=j]
      (fun s => @mapping_multiplicity R X Z F (A `&` P s) z)<=_).
  + apply: nonnegative_sum_mono=> s hs.
    rewrite /mapping_multiplicity composite_fibre_image.
    exact: counting_measure_image_bound.
  + apply: (@measure_disjoint_sum_bound R X [the choiceType of (seq nat : Type)]
      (@counting_measure R X) (counting_measure_is_measure R X)
      (mapping_fibre F A z) [set s | size s=j]
      (fun s => mapping_fibre F (A `&` P s) z)).
    * by move=> s hs x [[hx _] he]; split.
    * move=> s hs; exact: counting_measure_measurable.
    * move=> s t hs ht hst; apply/seteqP; split=> x; last by [].
      move=> [[[hx hxs] he] [[_ hxt] _]]; exfalso; apply: hst.
      apply: (@cover_partition_level_unique X E P hP s t x _ hxs hxt).
      by rewrite hs ht.
Qed.

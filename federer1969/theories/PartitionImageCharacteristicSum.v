(** The characteristic sums in Federer (1969), 2.10.10, p. 176: summing the
    characteristic functions of images of partition cells counts the cells
    meeting a fibre. The characteristic functions are used through their
    sealed zero/one laws, rather than exposed set membership decisions.
    Source context: MappingMultiplicity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  CountingMeasure PartitionHitCounts MappingMultiplicity CharacteristicFunctionUP
  CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partition_image_characteristic_sum]: the
    characteristic-sum interpretation in Federer 2.10.10,
    p. 176. The equality is pointwise and purely
    set theoretic, before any image-measurability premise
    is needed for integration. *)
Lemma partition_image_characteristic_sum (R : realType) (X Y : choiceType)
    (f : X -> Y) (A : set X) (P : seq nat -> set X) n y :
  nonnegative_sum [set s | size s=n]
    (fun s => (@CharacteristicFunction.value R Y (f @` (A `&` P s)) y)%:E)=
    @partition_hit_count R X P (mapping_fibre f A y) n.
Proof.
pose I := [set s | (f @` (A `&` P s)) y].
have he : [set s | size s=n] `&` I=partition_hit_indices P (mapping_fibre f A y) n.
  apply/seteqP; split=> s.
  - move=> [hs [x [hx hpx] hfx]]; split=> //.
    exists x; split=> //; by split.
  - move=> [hs [x [[hx hfx] hpx]]]; split=> //.
    exists x; first by split.
    exact hfx.
rewrite /partition_hit_count counting_measure_sum -he -nonnegative_sum_restrict.
apply: nonnegative_sum_ext=> s hs.
case: (pselect ((f @` (A `&` P s)) y))=> hy.
- have hmem : s \in I := mem_set hy.
  by rewrite hmem (characteristic_on_set (@CharacteristicFunction.laws R Y (f @` (A `&` P s))) hy).
- have hmem : s \notin I by apply/negP=> /set_mem hh; exact: hy hh.
  by rewrite (negbTE hmem) (characteristic_off_set (@CharacteristicFunction.laws R Y (f @` (A `&` P s))) hy).
Qed.

(** Federer (1969), 4.1.7, p. 358: finite
    compact pieces permit the Borel norm-density
    argument. This supporting lemma applies compact
    finiteness from 2.2.5, pp. 62–63, to the
    countably measurable definition of 2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP RadonBorelRegularity CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_compact_cover_countably_measurable]:
    a countable compact cover gives countable
    measurability, supporting Federer 4.1.7, p. 358,
    through 2.2.5 and 2.3.4. No finite total
    mass or nonempty-space condition is added. *)
Theorem radon_compact_cover_countably_measurable (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (C:nat->set X):
  (forall j,compact (C j)) ->setT `<=` \bigcup_j C j ->
  measure_countably_measurable mu setT.
Proof.
move=>hC hCover; exists (C @` setT); split.
- apply:sub_countable (card_image_le _ _) _; exact:countableP.
- split.
  + apply/seteqP; split.
    * move=>x hx; have [j _ hj]:=hCover x hx.
      exists (C j); first by exists j.
      exact:hj.
    * by move=>x _.
  + move=>K [j _ <-]; split.
    * exact:(@radon_compact_measurable R X mu hm hr (C j) (hC j)).
    * exact:(@radon_compact_finite R X mu hr (C j) (hC j)).
Qed.

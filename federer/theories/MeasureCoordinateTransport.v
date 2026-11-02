(** Coordinate identifications in Federer (1969), 2.6.5, pp. 119–120: finite
    products and Lebesgue measures use the usual Cartesian isomorphisms.
    These supporting lemmas transfer countable measurability and Borel
    regularity along bijections and homeomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasurePushforward PushforwardMeasurableSets
  CountablyMeasurableUP CountablyMeasurableSequences BorelRegularMeasureUP
  TopologicalBorel ContinuousBorelPreimages CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [bijective_pushforward_countably_measurable]: supporting
    invariance of the corrected countability hypothesis in Federer 2.6.5,
    pp. 119–120, under coordinate identifications *)
Lemma bijective_pushforward_countably_measurable (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> Y) (g : Y -> X) :
  cancel f g -> cancel g f -> measure_countably_measurable mu setT ->
  measure_countably_measurable (measure_pushforward f mu) setT.
Proof.
move=> hf hg hc.
have [A [hA hAm]] := (proj1 (@countably_measurable_sequence_iff R X mu hm setT)) hc.
apply/(countably_measurable_sequence_iff (measure_pushforward_is_measure f hm)).
exists (fun n => g @^-1` A n); split.
- apply/seteqP; split=> y _; last exact Logic.I.
  have [n _ hn] : (\bigcup_n A n) (g y) by rewrite -hA.
  by exists n.
- move=> n; have he : f @^-1` (g @^-1` A n) = A n.
    by apply/seteqP; split=> x /=; rewrite hf.
  split.
  + apply: pushforward_measurable_from_preimage; by rewrite he; exact: (hAm n).1.
  + by rewrite /measure_pushforward he; exact: (hAm n).2.
Qed.

(** Source for [homeomorphic_pushforward_borel_regular]: supporting
    transport of the Borel regularity asserted for Lebesgue products in
    Federer 2.6.5, p. 120 Both inverse identities and both continuity
    hypotheses are explicit. *)
Lemma homeomorphic_pushforward_borel_regular (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> Y) (g : Y -> X) :
  cancel f g -> cancel g f -> continuous f -> continuous g ->
  is_borel_regular_measure mu -> is_borel_regular_measure (measure_pushforward f mu).
Proof.
move=> hf hg hfc hgc hr; constructor.
- move=> U hU; apply: pushforward_measurable_from_preimage.
  apply: (@borel_regular_open_measurable R X mu hr (f @^-1` U)).
  apply: open_comp hU=> x _; exact: hfc.
- move=> A; have [B [hAB [hB he]]] := borel_regular_cover hr (f @^-1` A).
  exists (g @^-1` B); split.
  + move=> y hy; apply: hAB; by rewrite /= hg.
  + split; first exact (@continuous_borel_preimage Y X g hgc B hB).
    rewrite /measure_pushforward he.
    congr (mu _); apply/seteqP; split=> x /=; by rewrite hf.
Qed.

(** Source for [homeomorphic_countable_open_base]: supporting preservation
    of countable bases under the Euclidean coordinate identifications in
    Federer 2.6.5, p. 120. General topology background; the base is
    transported explicitly. *)
Lemma homeomorphic_countable_open_base (X Y : topologicalType)
    (f : X -> Y) (g : Y -> X) (U : nat -> set X) :
  cancel f g -> cancel g f -> continuous f -> continuous g ->
  is_countable_open_base U -> is_countable_open_base (fun n => g @^-1` U n).
Proof.
move=> hf hg hfc hgc hU; constructor.
- move=> n; apply: open_comp (countable_base_open hU n)=> y _; exact: hgc.
- by rewrite (countable_base_empty hU) preimage_set0.
- move=> V hV y hy.
  have hpre : open (f @^-1` V) by apply: open_comp hV=> x _; exact: hfc.
  have hgy : (f @^-1` V) (g y) by rewrite /= hg.
  have [n [hn hsub]] := countable_base_refines hU hpre hgy.
  exists n; split=> // z hz; have := hsub (g z) hz; by rewrite /= hg.
Qed.

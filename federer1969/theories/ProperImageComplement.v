(** Federer (1969), 2.2.17, p. 72: the complement of the image is open, so
    only sets contained in the image need attention in the printed argument.
    Source context: ProperMapUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward ProperMapUP ProperContinuousClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [proper_continuous_image_complement_open]: direct observation
    in Federer 2.2.17, p. 72, preceding the countable compact-slab
    construction. *)
Lemma proper_continuous_image_complement_open (X Y : topologicalType) (f : X -> Y) :
  hausdorff_space Y -> locally_compact (@setT Y) -> continuous f -> is_proper_map f ->
  open (~` (f @` setT)).
Proof.
move=> hY hl hf hp; apply: closed_openC.
exact: (@proper_continuous_map_closed X Y f hY hl hf hp setT closedT).
Qed.

(** Source for [pushforward_subset_outside_image_null]: supporting
    nullity of the outside-image contribution in Federer 2.2.17,
    p. 72. The inverse image is empty, so this
    uses only 2.1.2, pp. 53–54, without properness,
    continuity or a Radon hypothesis. *)
Lemma pushforward_subset_outside_image_null (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> Y) (B : set Y) :
  B `<=` ~` (f @` setT) -> measure_pushforward f mu B = 0.
Proof.
move=> hB; rewrite /measure_pushforward.
have he : f @^-1` B = set0.
  apply/seteqP; split; last by move=> x [].
  move=> x hx; apply: (hB (f x) hx); by exists x.
by rewrite he (measure_empty hm).
Qed.

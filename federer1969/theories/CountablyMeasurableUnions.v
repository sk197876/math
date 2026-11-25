(** Supporting countable-measurability facts for Federer (1969), 2.4.12, pp.
    86–87, especially the L-infinity completeness claim. The definition is
    Federer 2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_countable_union]: flattening
    the countable families in Federer 2.3.4, p. 76,
    supporting preservation of the Lp membership condition in
    Federer 2.4.12, pp. 86–87. *)
Lemma countably_measurable_countable_union (R : realType) (X I : choiceType)
    (mu : set X -> \bar R) (D : set I) (F : I -> set X) :
  countable D -> (forall i, measure_countably_measurable mu (F i)) ->
  measure_countably_measurable mu (\bigcup_(i in D) F i).
Proof.
move=> hD hF; pose C i := projT1 (cid (hF i)).
have hC i : countable (C i) /\ F i = \bigcup_(B in C i) B /\
    forall B, C i B -> measure_measurable mu B /\ mu B < +oo.
  exact: projT2 (cid (hF i)).
exists (\bigcup_(i in D) C i); split.
- apply: bigcup_countable hD _=> i _; exact: (hC i).1.
- split.
  + apply/seteqP; split=> x.
    * move=> [i hi hx]; rewrite (hC i).2.1 in hx; have [B hB hxB] := hx.
      exists B=> //; by exists i.
    * move=> [B [i hi hB] hx]; exists i=> //.
      rewrite (hC i).2.1; by exists B.
  + move=> B [i _ hB]; exact: (hC i).2.2 B hB.
Qed.

(** Source for [countably_measurable_binary_union]: finite union
    case of the supporting countable-family argument for
    Federer 2.4.12, pp. 86–87, using 2.3.4, p. 76. *)
Lemma countably_measurable_binary_union (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A B : set X) :
  measure_countably_measurable mu A -> measure_countably_measurable mu B ->
  measure_countably_measurable mu (A `|` B).
Proof.
move=> hA hB; have he : A `|` B = \bigcup_(b in @setT bool) (if b then A else B).
  apply/seteqP; split=> x.
  - move=> [hx|hx]; [by exists true|by exists false].
  - by move=> [[] _ hx]; [left|right].
rewrite he; apply: countably_measurable_countable_union (countableP setT) _.
by move=> [].
Qed.

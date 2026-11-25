(** Federer (1969), 3.2.22, pp. 259–260:
    exact fibre unions and omitted fibres for the
    chart-pair decomposition. These are set identities,
    with no measure or finite multiplicity premise. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [mapping_fibre_indexed_union]: the fibre
    decomposition in Federer 3.2.22, p. 260,
    commutes with the countable source-chart union.
    The set identity itself allows an arbitrary family. *)
Lemma mapping_fibre_indexed_union (X Y I:Type) (f:X->Y)
    (D:set I) (P:I->set X) z:
  mapping_fibre f (\bigcup_(i in D) P i) z=
    \bigcup_(i in D) mapping_fibre f (P i) z.
Proof.
apply/seteqP; split=>x.
- move=>[[i hi hx] hValue]; exists i; first exact hi; by split.
- move=>[i hi [hx hValue]]; split; last exact hValue; by exists i.
Qed.

(** Source for [mapping_fibre_chart_remainder]: the
    omitted source fibres retained in the corrected
    proof of Federer 3.2.22, pp. 258–260.
    Pulling back the target point turns omission of
    the chart union into omission of its fibre union. *)
Lemma mapping_fibre_chart_remainder (X Y I:Type) (f:X->Y)
    (W:set X) (D:set I) (P:I->set X) z:
  mapping_fibre f (W `\` (\bigcup_(i in D) P i)) z=
    mapping_fibre f W z `\` (\bigcup_(i in D) mapping_fibre f (P i) z).
Proof.
apply/seteqP; split=>x.
- move=>[[hw hNot] hValue]; split; first by split.
  move=>[i hi [hPi _]]; apply:hNot; by exists i.
- move=>[[hw hValue] hNot]; split; last exact hValue; split; first exact hw.
  move=>[i hi hPi]; apply:hNot; exists i; first exact hi; by split.
Qed.

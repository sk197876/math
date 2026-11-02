(** Federer (1969), 3.2.14(2), p. 251:
    flattening countable rectifiable families. Every
    selected family is used only inside the proof;
    the definition itself remains an abstract predicate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RectifiableSetUP RectifiableElementary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_rectifiable_countable_union]:
    closure under countable unions of the countable
    family definition, Federer 3.2.14(2), p. 251. *)
Theorem countably_rectifiable_countable_union (R : realType)
    (X : metricType R) (I : choiceType) m (D : set I) (F : I -> set X) :
  countable D -> (forall i, D i -> is_countably_m_rectifiable m (F i)) ->
  is_countably_m_rectifiable m (\bigcup_(i in D) F i).
Proof.
move=> hD hF.
have hex i : exists C : set (set X), countable C /\
    (forall G, C G -> is_m_rectifiable m G) /\
    (D i -> F i=\bigcup_(G in C) G).
  case: (pselect (D i))=> [hi|hi].
  - have [C [hc [hC hr]]] := hF i hi.
    exists C; split=> //; split=> // _; exact hr.
  - exists set0; split; first exact: countable0.
    split; first by move=> G [].
    by move=> /hi.
have [C hC] := choice hex.
exists (\bigcup_(i in D) C i); split.
- apply: bigcup_countable hD _=> i hi; exact: (hC i).1.
- split.
  + move=> G [i hi hG]; exact: (hC i).2.1 G hG.
  + apply/seteqP; split=> x.
    * move=> [i hi hx]; rewrite ((hC i).2.2 hi) in hx.
      have [G hG hGx] := hx; exists G=> //; by exists i.
    * move=> [G [i hi hG] hx]; exists i=> //.
      rewrite ((hC i).2.2 hi); by exists G.
Qed.

(** Source for [countably_rectifiable_binary_union]:
    the two-member family case of Federer 3.2.14(2),
    p. 251. This does not require boundedness of the union. *)
Lemma countably_rectifiable_binary_union (R : realType)
    (X : metricType R) m (E F : set X) :
  is_countably_m_rectifiable m E -> is_countably_m_rectifiable m F ->
  is_countably_m_rectifiable m (E `|` F).
Proof.
move=> hE hF.
have he : E `|` F=\bigcup_(b in @setT bool) (if b then E else F).
  apply/seteqP; split=> x.
  - move=> [hx|hx]; [by exists true|by exists false].
  - by move=> [[] _ hx]; [left|right].
rewrite he; apply: countably_rectifiable_countable_union (countableP setT) _.
by move=> [].
Qed.

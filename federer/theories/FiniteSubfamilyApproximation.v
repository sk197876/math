(** Federer (1969), proof of 2.8.2, p. 143: replace the countable selected
    family H by a sufficiently large finite subfamily. No measurability of
    the later target B_i is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure MeasureFinitePrefixError SetSequenceDisjointification
  CountableFamilySequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_subfamily_measure_error]: the finite selection step
    of Federer 2.8.2, p. 143. A finite subfamily retains every strict bound
    on the limiting uncovered measure. Disjointness is not needed for this
    auxiliary approximation. Empty families are retained by zero-filled
    enumeration; empty padding is removed from the chosen subfamily whenever
    it is ineligible. *)
Lemma finite_subfamily_measure_error (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (W : set X) (H : set (set X)) (e : \bar R) :
  measure_measurable mu W -> mu W < +oo -> countable H ->
  (forall B, H B -> measure_measurable mu B) ->
  mu (W `\` \bigcup_(B in H) B) < e ->
  exists G : set (set X), G `<=` H /\ finite_set G /\
    mu (W `\` \bigcup_(B in G) B) < e.
Proof.
move=> hW hWf hH hmeas he.
have [E [hE hU]] := @countable_family_as_sequence X [the choiceType of set X]
  H idfun hH.
have hEm n : measure_measurable mu (E n).
  case: (hE n)=> [->|[B [hB ->]]]; first exact: measure_measurable_empty hm.
  exact: hmeas B hB.
have he' : mu (W `\` \bigcup_n E n) < e by rewrite hU.
have [N hN] := @measure_finite_prefix_error R X mu hm W E e hW hWf hEm he'.
pose G : set (set X) := (E @` `I_N) `&` H.
have hfin : finite_set G.
  apply: (sub_finite_set (B:= E @` `I_N)).
  - by move=> B [].
  - exact: finite_image E (finite_II N).
have hGU : (\bigcup_(B in G) B) = set_sequence_prefix E N.
  apply/seteqP; split.
  - move=> x [B [[n hn heB] hBH] hx].
    exists n=> //; by rewrite heB.
  - move=> x [n hn hx].
    have hmem : H (E n).
      case: (hE n)=> [he0|[B [hB heB]]].
      + exfalso; by move: hx; rewrite he0.
      + by rewrite heB.
    exists (E n)=> //; split=> //; by exists n.
exists G; split; first by move=> B [].
split=> //; by rewrite hGU.
Qed.

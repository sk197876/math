(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP CoveringFamilyUP CoveringFamilyLaws CountableAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [adequate_countable_indexed_almost_cover]: supporting
    countable cutoff reduction in Federer 2.9.15, p. 160,
    using 2.8.3, p. 143. Adequacy on a countably indexed
    family covering almost all of Z extends to Z by adding
    the null remainder as one adequate target. This avoids
    an arbitrary encoding of pairs of natural cutoffs. *)
Lemma adequate_countable_indexed_almost_cover (R : realType) (X : metricType R)
    (J : choiceType) (phi : set X -> \bar R) (F : set (set X))
    (Z : set X) (D : set J) (A : J -> set X) :
  is_covering_theory_context F phi -> countable D ->
  (forall j, D j -> family_is_measure_adequate phi F (A j)) ->
  phi (Z `\` \bigcup_(j in D) A j)=0 -> family_is_measure_adequate phi F Z.
Proof.
move=> hc hD ha hz.
pose E := Z `\` \bigcup_(j in D) A j.
pose K := \bigcup_(b in @setT bool) (if b then A @` D else [set E]).
have hK : countable K.
  apply: bigcup_countable (countableP setT) _=> b _; case: b.
  - exact: sub_countable (card_image_le A D) hD.
  - exact: countable1.
have hAdeq B : K B -> family_is_measure_adequate phi F B.
  move=> [b _ hB]; case: b hB=> /=.
  - by move=> [j hj <-]; exact: ha j hj.
  - move=> ->; exact: (@adequate_family_null_target R X phi (covering_context_measure hc) F E hz).
have hcover : Z `<=` \bigcup_(B in K) B.
  move=> x hx; case: (pselect ((\bigcup_(j in D) A j) x))=> [[j hj hxj]|hn].
  - exists (A j)=> //; exists true=> //; by exists j.
  - exists E; last by split.
    by exists false.
exact: (@adequate_family_mono_set R X phi (covering_context_measure hc) F Z _ hcover
  (@adequate_family_countable_union R X F K phi hc hK hAdeq)).
Qed.

(** The last reduction of Federer (1969), 2.8.17, p. 152, from countably
    many adequate targets covering almost all of Z to adequacy for Z. The
    null remainder is an additional adequate target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP CoveringFamilyUP CoveringFamilyLaws CountableAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [adequate_family_countable_almost_cover]: the
    final sentence of the proof of Federer 2.8.17, p. 152.
    The cited 2.8.2 is corrected to 2.8.3 in the erratum,
    p. 3, book p. 152 line 10. This supporting form
    allows arbitrary, possibly nonmeasurable targets. *)
Lemma adequate_family_countable_almost_cover (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X)) (Z : set X) (A : nat -> set X) :
  is_covering_theory_context F phi ->
  (forall n, family_is_measure_adequate phi F (A n)) ->
  phi (Z `\` \bigcup_(n in @setT nat) A n) = 0 -> family_is_measure_adequate phi F Z.
Proof.
move=> hc ha hz.
pose E := Z `\` \bigcup_(n in @setT nat) A n.
pose T n := match n with 0%N => E | n.+1 => A n end.
pose K := T @` (@setT nat).
have hK : countable K := sub_countable (card_image_le T setT) (countableP setT).
have hT B : K B -> family_is_measure_adequate phi F B.
  move=> [n _ <-]; case: n=> [|n] /=; last exact: ha.
  exact (@adequate_family_null_target R X phi (covering_context_measure hc) F E hz).
have hcover : Z `<=` \bigcup_(B in K) B.
  move=> x hx; case: (pselect ((\bigcup_(n in @setT nat) A n) x))=> [[n _ hn]|hn].
  - exists (T n.+1); last exact hn; by exists n.+1.
  - exists (T 0%N); last by split.
    by exists 0%N.
exact (@adequate_family_mono_set R X phi (covering_context_measure hc) F Z _ hcover
  (@adequate_family_countable_union R X F K phi hc hK hT)).
Qed.

(** Federer (1969), Theorem 2.8.7, p. 144: bounded nonnegative weights, a
    fine covering, and strict control of enlargement measure give adequacy.
    The initial reduction uses 2.8.3. We retain Federer's lambda>1 *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CoveringFamilyUP
  FiniteOpenMeasureCover CountableAdequacy FiniteEnlargementAdequacy
  WeightedEnlargements FamilyWeightedEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Adequacy.
Variable R : realType.
Variable X : metricType R.
Variable F : set (set X).
Variable mu : set X -> \bar R.
Variable d : set X -> R.
Variables tau lambda : R.
Variable A : set X.
Variable hc : is_covering_theory_context F mu.
Variable hnon : forall S, F S -> (0 <= d S)%R.
Variable hbounded : exists C, forall S, F S -> (d S <= C)%R.
Variable ht : (1 < tau)%R.
Variable hl : (1 < lambda)%R.
Variable hbound : forall S, F S ->
  mu (weighted_enlargement F d tau S) < lambda%:E * mu S.
Variable hf : family_covers_finely F A.

(** Source for [enlargement_adequate_finite_open_target]: Supporting Federer
    2.8.7, p. 144.For A intersect U test the local theorem on V intersect U.
    The target A itself need not be measurable or have finite measure. *)
Lemma enlargement_adequate_finite_open_target U : open U -> mu U < +oo ->
  family_is_measure_adequate mu F (A `&` U).
Proof.
move=> hU hUf V hV.
have hW : open (V `&` U) := openI hV hU.
have hWf : mu (V `&` U) < +oo.
  apply: le_lt_trans (@measure_mono R X mu (covering_context_measure hc) _ U _) hUf.
  by move=> x [].
have [G hG] := @finite_open_enlargement_adequacy R X F mu d tau lambda A
  hc hnon hbounded ht hl hbound hf (V `&` U) hW hWf.
exists G; constructor.
- exact: adequate_selection_members hG.
- exact: adequate_selection_countable hG.
- exact: adequate_selection_disjoint hG.
- move=> x hx; exact: (adequate_selection_within hG hx).1.
- have he : V `&` (A `&` U) = (V `&` U) `&` A.
    apply/seteqP; split.
    * by move=> x [hv [ha hu]]; split=> //; split.
    * by move=> x [[hv hu] ha]; split=> //; split.
  rewrite he; exact: adequate_selection_remainder hG.
Qed.

(** Source for [enlargement_control_adequacy]: the reduction by 2.8.3 at the
    start of Federer 2.8.7, p. 144, with the open finite-measure cover
    detailed. This auxiliary statement represents the weight by a total
    function, used only on F. *)
Theorem enlargement_control_adequacy : family_is_measure_adequate mu F A.
Proof.
have [U hU] := covering_context_finite_open_cover hc.
pose f n := A `&` U n.
pose K := f @` (@setT nat).
have hK : countable K := sub_countable (card_image_le f setT) (countableP setT).
have ha B : K B -> family_is_measure_adequate mu F B.
  move=> [n _ <-]; exact: enlargement_adequate_finite_open_target
    (@finite_open_cover_open R X mu U hU n) (@finite_open_cover_finite R X mu U hU n).
have he : (\bigcup_(B in K) B) = A.
  apply/seteqP; split.
  - by move=> x [B [n _ <-] [hxA _]].
  - move=> x hx.
    have [n _ hn] := @finite_open_cover_covers R X mu U hU x Logic.I.
    exists (f n); last by split.
    by exists n.
have h := @adequate_family_countable_union R X F K mu hc hK ha.
by rewrite he in h.
Qed.
End Adequacy.

(** Source for [federer_2_8_7]: direct formalisation of Federer 2.8.7, p.
    144: F covers A finely, delta is a bounded nonnegative function on F,
    tau>1, lambda>1, and phi(hat S)<lambda phi(S) for each eligible S. Then
    F is phi adequate for A. The standing hypotheses are exactly those of
    2.8.1. No target measurability, Borel regularity, or positive-weight
    premise is added. *)
Theorem federer_2_8_7 (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) (A : set X)
    (delta : {S : set X | F S} -> R) (tau lambda : R) :
  is_covering_theory_context F mu -> family_covers_finely F A ->
  (forall S, (0 <= delta S)%R) -> (exists C, forall S, (delta S <= C)%R) ->
  (1 < tau)%R -> (1 < lambda)%R ->
  (forall S, mu (family_weighted_enlargement delta tau S) < lambda%:E * mu (sval S)) ->
  family_is_measure_adequate mu F A.
Proof.
move=> hc hf hnon hbounded ht hl hbound.
have [d hd] := @family_weight_extension_exists R X F delta.
have hn S (hS : F S) : (0 <= d S)%R by rewrite (hd S hS); exact: hnon.
have hb : exists C, forall S, F S -> (d S <= C)%R.
  have [C hC] := hbounded; exists C=> S hS; rewrite (hd S hS); exact: hC.
have he S (hS : F S) : mu (weighted_enlargement F d tau S) < lambda%:E * mu S.
  rewrite (@family_weighted_enlargement_extension R X F delta d tau hd (exist F S hS)).
  exact: hbound (exist F S hS).
exact (@enlargement_control_adequacy R X F mu d tau lambda A hc hn hb ht hl he hf).
Qed.

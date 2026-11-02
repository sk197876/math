(** Federer (1969), proof of 2.8.2, p. 142, first sentence This module
    proves the reduction for any cover satisfying its abstract laws; it does
    not unfold either sealed selection witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CoveringFamilyUP
  CoveringFamilyLaws ContractionCoverUP FiniteOpenMeasureCover
  OpenRestrictionContraction FiniteTargetContractionCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_target_contraction_adequacy]: the general-target
    case of Federer 2.8.2, pp. 142–143, with the omitted reduction spelled
    out. Representatives s(B), t(B) assign one original contraction factor
    to each restricted target. Neither target measurability nor separability
    is assumed. *)
Theorem countable_target_contraction_adequacy (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F K : set (set X)) (sigma : set X -> R) (U : nat -> set X) :
  (forall B, F B -> closed B) ->
  (forall V, open V -> measure_measurable mu V) ->
  is_finite_open_measure_cover mu U -> countable K ->
  (forall T, K T -> (0 < sigma T < 1)%R) ->
  (forall T, K T -> has_local_cover_contraction mu F T (sigma T)) ->
  family_is_measure_adequate mu F (\bigcup_(T in K) T).
Proof.
move=> hF hopen hU hK hsigma hlocal.
case: (pselect (exists A, K A))=> [[A0 hA0]|hempty].
- pose J := K `*` (@setT nat).
  pose f (p : set X * nat) := p.1 `&` U p.2.
  pose L := f @` J.
  have hJ : countable J by apply: countableX=> //; exact: countableP.
  have hL : countable L := sub_countable (card_image_le f J) hJ.
  have hex B : L B -> exists p, J p /\ B = f p.
    by move=> [p hp he]; exists p; split=> //; symmetry.
  pose rep B := match pselect (L B) with
    | left h => projT1 (cid (hex B h))
    | right _ => (A0,0%N)
    end.
  have hrep B (hB : L B) : J (rep B) /\ B = f (rep B).
    rewrite /rep; case: (pselect (L B))=> [h|h]; last by contradiction.
    exact: projT2 (cid (hex B h)).
  pose tau B := sigma (rep B).1.
  have hfinite B (hB : L B) : mu B < +oo.
    have [hp he] := hrep B hB; rewrite he /f.
    apply: le_lt_trans (@measure_mono R X mu hm _ (U (rep B).2) _) _.
    * by move=> x [].
    * exact (@finite_open_cover_finite R X mu U hU (rep B).2).
  have htau B (hB : L B) : (0 < tau B < 1)%R.
    exact: hsigma _ (hrep B hB).1.1.
  have hloc B (hB : L B) : has_local_cover_contraction mu F B (tau B).
    have [hp he] := hrep B hB; rewrite {1}he /f /tau.
    apply: local_contraction_open_restriction.
    * exact (@finite_open_cover_open R X mu U hU (rep B).2).
    * exact (hlocal (rep B).1 hp.1).
  have he : (\bigcup_(B in L) B) = (\bigcup_(A in K) A).
    apply/seteqP; split.
    * move=> x [B hB hx]; have [hp hb] := hrep B hB.
      rewrite hb /f in hx.
      exists (rep B).1; first exact hp.1.
      exact hx.1.
    * move=> x [A hA hx].
      have [n _ hn] := @finite_open_cover_covers R X mu U hU x Logic.I.
      exists (A `&` U n); last by split.
      exists (A,n); first by split.
      by [].
  rewrite -he.
  exact (@finite_target_contraction_adequacy R X mu hm F L tau
    hF hopen hL hfinite htau hloc).
- have he : (\bigcup_(T in K) T) = set0.
    apply/seteqP; split=> [x [T hT _]|x []].
    exfalso; apply: hempty; by exists T.
  rewrite he; exact (@adequate_family_empty_target R X mu hm F).
Qed.

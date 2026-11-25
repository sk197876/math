(** Federer (1969), 2.8.18, p. 152: centered closed balls form a Vitali
    relation on a separable metric space covered by countably many
    directionally limited targets. The theorem here retains Federer's exact
    countable coverage and original directional definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP CoveringFamilyLaws
  CoveringRelationUP CoveringRelationCutoffs CenteredBallRelations CenteredBallFamilyCaps
  MetricSubsetBackground MetricSubsetSeparability DirectionalLimitationUP DirectionalLimitationLaws
  CenteredBallFineness CenteredBallAdequacy CountableAdequacy TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_8_18]: direct formalisation of the
    complete theorem in Federer 2.8.18, p. 152.
    The proof retains its application of 2.8.15 to A
    intersect Z, followed by countable adequacy 2.8.3.
    Hereditary separability and the small-radius family restriction
    are proved explicitly; original relation fineness is converted
    to centered radius fineness without assuming diameter=2r. *)
Theorem federer_2_8_18 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (K : set (set X)) :
  is_covering_theory_context
    (covering_relation_image (@centered_closed_ball_relation R X) setT) phi ->
  (exists D : set X, countable D /\ dense D) -> countable K ->
  (\bigcup_(A in K) A) = setT ->
  (forall A, K A -> exists (xi : \bar R) (eta : R) (zeta : nat),
    is_directionally_limited_at A xi eta zeta) ->
  is_vitali_relation phi (@centered_closed_ball_relation R X).
Proof.
move=> hc hsep hK hcover hdir.
pose V := @centered_closed_ball_relation R X.
constructor.
- exact: centered_closed_balls_covering.
- move=> S hS; exact: closed_borel_set (covering_context_closed hc hS).
- exact: centered_closed_balls_fine.
- move=> C Z hCV hCfine.
  pose F := covering_relation_image C Z.
  have hFV : F `<=` covering_relation_image V setT.
    move=> S [x [_ hx]]; exists x; split=> //; exact: hCV x S hx.
  have hFc := @covering_context_subfamily R X phi _ F hc hFV.
  have hrad := @fine_centered_relation_small_radii R X C Z hCV hCfine.
  pose L := (fun A : set X => A `&` Z) @` K.
  have hL : countable L := sub_countable (card_image_le _ K) hK.
  have hAdeq B : L B -> family_is_measure_adequate phi F B.
    move=> [A hA <-].
    have [xi [eta [zeta hlim]]] := hdir A hA.
    have [mu [hm hsmall]] := @positive_directional_radius_cap R xi (directional_radius_positive hlim).
    pose H := capped_closed_ball_family F mu.
    have hHF : H `<=` F by move=> S [hS _].
    have hHc := @covering_context_subfamily R X phi F H hFc hHF.
    have hlimAZ : is_directionally_limited_at (A `&` Z) xi eta zeta.
      apply: (@directional_limit_subset R X (A `&` Z) A xi eta zeta) hlim.
      by move=> x [].
    have hradAZ : has_arbitrarily_small_centered_balls F (A `&` Z).
      by move=> x [_ hx]; exact: hrad x hx.
    have hcap := @capped_closed_balls_remain_fine R X F (A `&` Z) mu hm hradAZ.
    have hinf := (centered_radius_infimum_zero_iff_small_balls H (A `&` Z)).2 hcap.
    have hsepAZ := @metric_subset_separable R X (A `&` Z) hsep.
    have ha := @federer_2_8_15 R X phi H (A `&` Z) xi eta mu zeta hHc hlimAZ hm hsmall
      (@capped_closed_balls_small_family R X F mu) hsepAZ hinf.
    exact (@adequate_family_mono_family R X phi H F (A `&` Z) hHF ha).
  have hZ : (\bigcup_(B in L) B) = Z.
    apply/seteqP; split.
    + by move=> x [B [A hA <-] [_ hx]].
    + move=> x hx.
      have hxK : (\bigcup_(A in K) A) x by rewrite hcover.
      have [A hA hxA] := hxK.
      exists (A `&` Z); last by split.
      by exists A.
  have ha := @adequate_family_countable_union R X F L phi hFc hL hAdeq.
  rewrite hZ in ha.
  have [G hG] := ha setT openT.
  exists G; split; first exact: adequate_selection_members hG.
  split; first exact: adequate_selection_countable hG.
  split; first exact: adequate_selection_disjoint hG.
  by have := adequate_selection_remainder hG; rewrite setTI.
Qed.

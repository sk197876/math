(** The local contraction step in Federer (1969), 2.8.15, p. 150. Localize
    the centered small balls to an open set, apply 2.8.14, prove the color
    classes countable by target separability, and choose a measurable color
    union with the required contraction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureCountableClosure MetricSubsetBackground
  CoveringFamilyUP CoveringFamilyLaws ContractionCoverUP DirectionalLimitationUP
  DirectionalLimitationLaws CenteredBallCoverUP CenteredBallCover
  DisjointDenseBallFamilies CenteredBallFineness FiniteCoverContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [localized_countable_ball_color_cover]: the
    families H_1,...,H_(2 zeta+1) in Federer 2.8.15, p. 150.
    They are countable and disjointed, lie inside the testing
    open set, cover its intersection with A, and have measurable
    unions. Target separability suffices; A need not be measurable. *)
Theorem localized_countable_ball_color_cover (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X)) (A W : set X)
    (xi : \bar R) (eta mu : R) (zeta : nat) :
  is_covering_theory_context F phi -> is_directionally_limited_at A xi eta zeta ->
  0 < mu -> (mu%:E < (1/2 : R)%:E * xi)%E ->
  (exists D : set (metric_subset A), countable D /\ dense D) ->
  has_arbitrarily_small_centered_balls F A -> open W ->
  exists G : 'I_(2*zeta+1) -> set (set X),
    is_finite_disjoint_ball_cover F (W `&` A) G /\
    forall i, countable (G i) /\ (\bigcup_(B in G i) B) `<=` W /\
      measure_measurable phi (\bigcup_(B in G i) B).
Proof.
move=> hc hlim hm hsmall hsep hf hW.
pose F' := localized_centered_ball_family F A W mu.
have hWA : W `&` A `<=` A by move=> a [_ ha].
have hlim' := directional_limit_subset hWA hlim.
have hF' : is_small_closed_ball_family mu F' := @localized_centered_balls_small_family R X F A W mu.
have hcenter : has_small_centered_balls mu F' (W `&` A) :=
  fine_centered_balls_open_localization hf hW hm.
have [G hG] := @federer_2_8_14 R X (W `&` A) xi eta mu zeta F' hlim' hm hsmall hF' hcenter.
have hGF i B : G i B -> F' B.
  exact: (@finite_ball_cover_members X F' (W `&` A) (2*zeta+1)%N G hG i B).
have hmem i B : G i B -> F B by move=> hB; exact: (hGF i B hB).1.
exists G; split.
- constructor.
  + exact hmem.
  + exact: finite_ball_cover_disjoint hG.
  + exact: finite_ball_cover_covers hG.
- move=> i.
  have hballs : positive_ball_family_centered_on A (G i).
    move=> B hB; apply: (@localized_centered_balls_centered_on_target R X F A W mu B).
    exact: hGF i B hB.
  have hcount : countable (G i) := @separable_centered_disjoint_balls_countable R X A
    (G i) hsep hballs (@finite_ball_cover_disjoint X F' (W `&` A) (2*zeta+1)%N G hG i).
  split=> //; split.
  + move=> x [B hB hx]; exact: (hGF i B hB).2.1 x hx.
  + apply: (@measure_measurable_countable_union R X [the choiceType of set X]
      phi (covering_context_measure hc) (G i) id hcount)=> B hB.
    exact (@covering_context_member_measurable R X F phi hc B (hmem i B hB)).
Qed.

(** Source for [centered_fine_cover_local_contraction]: the hypothesis of
    2.8.2 with sigma=2 zeta/(2 zeta+1) in Federer 2.8.15, p. 150. The
    intermediate scalar is 1-1/(2 zeta+1), with its printed fraction
    identity proved in FiniteCoverContraction.v. *)
Theorem centered_fine_cover_local_contraction (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X)) (A : set X)
    (xi : \bar R) (eta mu : R) (zeta : nat) :
  is_covering_theory_context F phi -> is_directionally_limited_at A xi eta zeta ->
  0 < mu -> (mu%:E < (1/2 : R)%:E * xi)%E ->
  (exists D : set (metric_subset A), countable D /\ dense D) ->
  has_arbitrarily_small_centered_balls F A ->
  has_local_cover_contraction phi F A (finite_cover_loss_factor R (2*zeta+1)%N).
Proof.
move=> hc hlim hm hsmall hsep hf W hW.
pose N := (2*zeta+1)%N.
have hZ := directional_cardinal_positive hlim.
have htwo : (0 < 2*zeta)%N by rewrite muln_gt0 hZ.
have hN1 : (1 < N)%N by rewrite /N addn1 ltnS.
have hN : (0 < N)%N := ltn_trans (ltnSn 0) hN1.
have hsigma := @finite_cover_loss_factor_range R N hN1.
have hphi := covering_context_measure hc.
case: (ltP (phi (W `&` A)) +oo)%E=> [hfinite|hinfty].
- have [G [hG hprops]] := @localized_countable_ball_color_cover R X phi F A W
    xi eta mu zeta hc hlim hm hsmall hsep hf hW.
  pose U i := \bigcup_(B in G i) B.
  have hmeas i : measure_measurable phi (U i) := (hprops i).2.2.
  have hcover : W `&` A `<=` \bigcup_(i in @setT 'I_N) U i := finite_ball_cover_covers hG.
  have [i hi] := @finite_measurable_cover_contraction R X phi hphi (W `&` A) N U
    hN hfinite hmeas hcover.
  exists (G i); split; first exact: (hprops i).1.
  constructor.
  + exact: finite_ball_cover_members hG i.
  + exact: finite_ball_cover_disjoint hG i.
  + exact: (hprops i).2.1.
  + exact hi.
- have he : phi (W `&` A) = +oo%E by apply/eqP; rewrite eq_le leey hinfty.
  exists set0; split; first exact: countable0.
  constructor.
  + by move=> B [].
  + by move=> B C [].
  + by move=> x [B []].
  + rewrite bigcup_set0 setD0 he gt0_muley //.
    by rewrite lte_fin; exact: (andP hsigma).1.
Qed.

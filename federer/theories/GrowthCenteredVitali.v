(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic BorelRegularMeasureUP
  MeasureDerivationContext NullBallLocus FivefoldBallGrowth UniformBallGrowthAdequacy
  IndexedAdequacyAlmostCover CoveringFamilyUP CoveringFamilyLaws CoveringRelationUP
  CoveringRelationFineness CenteredBallRelations MetricClosedBalls TopologicalBorel
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_subrelation_covering_context]: supporting
    covering context for the first proof paragraph of Federer
    2.9.15, p. 160. Members of C(Z) are closed balls;
    the standing class M supplies open-set measurability and
    finite mass on bounded sets. The target Z is arbitrary. *)
Lemma centered_subrelation_covering_context (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (C : X -> set X -> Prop) (Z : set X) :
  is_derivation_measure phi ->
  (forall x S, C x S -> centered_closed_ball_relation x S) ->
  is_covering_theory_context (covering_relation_image C Z) phi.
Proof.
move=> hphi hC; constructor.
- exact: derivation_measure_law hphi.
- move=> S [x [_ hS]]; have [r [_ ->]] := hC x S hS.
  exact: metric_closed_ball_closed.
- exact: borel_regular_open_measurable (derivation_measure_borel_regular hphi).
- exact: derivation_measure_bounded_finite hphi.
Qed.

(** Source for [fivefold_growth_centered_balls_vitali]: the
    first alternative's centered-ball Vitali assertion in the
    proof of Federer 2.9.15, p. 160. Countable uniform
    cutoff pieces reduce to the diameter-enlargement adequacy
    theorem 2.8.7, underlying 2.8.17. Add the null-ball
    locus P using the section's standing Vitali relation.
    This expands the printed application while respecting the
    positivity correction to 2.8.17 (erratum p. 3, book
    p. 151 line 24) without globally positive ball masses. *)
Theorem fivefold_growth_centered_balls_vitali (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V0 : X -> set X -> Prop) :
  is_measure_derivation_context phi V0 ->
  (forall x, fivefold_ball_ratio_upper_limit phi x< +oo) ->
  is_vitali_relation phi (@centered_closed_ball_relation R X).
Proof.
move=> hc0 hgrowth; have hphi := derivation_context_measure hc0.
have hm := derivation_measure_law hphi.
constructor.
- exact: centered_closed_balls_covering.
- move=> S [x [_ [r [_ ->]]]]; apply: closed_borel_set; exact: metric_closed_ball_closed.
- exact: centered_closed_balls_fine.
- move=> C Z hC hCf.
  pose F := covering_relation_image C Z.
  have hFctx := @centered_subrelation_covering_context R X phi C Z hphi hC.
  pose A (p : (nat*nat)%type) := Z `&` [set x | forall r : R, (0<r)%R ->
    (r<((p.2.+1%:R : R)^-1))%R ->
    phi (metric_closed_ball x (5*r)%R)<((p.1+2)%:R : R)%:E*phi (metric_closed_ball x r)].
  have hAdeq p : family_is_measure_adequate phi F (A p).
    have hAf x : A p x -> covering_relation_fine_at C x by move=> [hx _]; exact: hCf x hx.
    have hdelta : (0<(p.2.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
    have hlambda : (1<(p.1+2)%:R :> R)%R by rewrite ltr1n addn2 !ltnS leq0n.
    have hAg : has_uniform_fivefold_ball_growth phi (A p)
        ((p.2.+1%:R : R)^-1)%R ((p.1+2)%:R : R).
      by move=> x [_ hb] r; exact: hb r.
    have ha := @centered_uniform_growth_subrelation_adequate R X phi C (A p)
      ((p.2.+1%:R : R)^-1)%R ((p.1+2)%:R : R) hphi hC hAf hdelta hlambda hAg.
    apply: (@adequate_family_mono_family R X phi (covering_relation_image C (A p)) F (A p) _ ha).
    by move=> S [x [[hx _] hS]]; exists x.
  have hnull : phi (Z `\` \bigcup_p A p)=0.
    apply: (@measure_null_subset R X phi hm _ (measure_null_ball_points phi) _
      (@measure_null_ball_points_null R X phi V0 hc0)).
    move=> x [hxZ hn]; apply: contrapT=> hxP; apply: hn.
    have [lambda [d [hl [hd hb]]]] := @finite_fivefold_ball_growth_cutoff R X phi x hphi hxP (hgrowth x).
    have hln : (0<=lambda)%R := ltW (lt_trans ltr01 hl).
    pose n := Num.bound lambda.
    have hnat : (lambda<(n+2)%:R)%R.
      apply: lt_le_trans (archi_boundP hln) _; by rewrite ler_nat leq_addr.
    have [m hmcut] := @positive_reciprocal_nat_small R d hd.
    exists (n,m)=> //; split=> // r hr hrd.
    have hsmall : (r<d)%R := lt_trans hrd hmcut.
    apply: lt_le_trans (hb r hr hsmall) _.
    have hco : lambda%:E<=((n+2)%:R : R)%:E by rewrite lee_fin; exact: ltW hnat.
    exact: (@lee_wpmul2r R (phi (metric_closed_ball x r))
      (@measure_nonnegative R X phi hm (metric_closed_ball x r)) _ _ hco).
  have hAdeqZ := @adequate_countable_indexed_almost_cover R X (nat*nat)%type phi F Z setT A
    hFctx (countableP _) (fun p _ => hAdeq p) hnull.
  have [G hG] := hAdeqZ setT openT.
  exists G; split; first exact: adequate_selection_members hG.
  split; first exact: adequate_selection_countable hG.
  split; first exact: adequate_selection_disjoint hG.
  by have := adequate_selection_remainder hG; rewrite setTI.
Qed.

(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext BorelRegularMeasureUP TopologicalBorel MetricSetDistanceUP MetricSetDistanceSealed
  UniformBallGrowthAdequacy StrictFivefoldGrowth CenteredBallRelations GrowthCenteredVitali
  MeasureDensityPoints DensityMeasurableSets ClosedBallRatioBounds NaturalBallRatioBounds
  RadialBallRatios ClosedTargetRatioDecay MeasurableClosedAlmostCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [has_zero_or_infinite_upper_ball_ratio]: direct
    alternative in Federer 2.9.17, p. 162:
    the upper positive-radius ball ratio equals zero or
    positive infinity. The ratio limsup is the actual
    partial-quotient radius limsup, not an ordinary derivate. *)
Definition has_zero_or_infinite_upper_ball_ratio (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) : set X :=
  [set x | centered_ball_ratio_upper_limit psi phi x=0 \/
    centered_ball_ratio_upper_limit psi phi x= +oo].

(** Source for [closed_uniform_bound_ratio_zero]: direct
    almost-everywhere zero ratio limit on C_n in Federer
    2.9.17, p. 162. The corrected covering
    criterion gives the centered Vitali property, and 2.9.11
    gives zero complement density almost everywhere on the
    closed set. The previously proved covering estimate then
    yields zero upper radial ratio there. *)
Lemma closed_uniform_bound_ratio_zero (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop)
    (A : set X) (c delta lambda mu : R) :
  is_measure_derivation_context phi V0 -> is_measure psi -> closed A ->
  (0<=c)%R -> (0<delta)%R -> (0<lambda)%R -> (0<mu)%R ->
  has_uniform_fivefold_ball_growth phi setT mu lambda ->
  (forall z, A z -> bounded_centered_ball_ratio_locus psi phi c delta z) ->
  psi A=0 -> phi (A `\` [set x | centered_ball_ratio_upper_limit psi phi x=0])=0.
Proof.
move=> hc0 hpsi hA hc hdelta hl hmu hg hbound hnull.
have hphi := derivation_context_measure hc0.
have hm := derivation_measure_law hphi.
have hgrowth := @strict_fivefold_growth_finite_upper_limit R X phi lambda mu hphi hmu hg.
have hV := @fivefold_growth_centered_balls_vitali R X phi V0 hc0 hgrowth.
have hctx : is_measure_derivation_context phi (@centered_closed_ball_relation R X).
  by constructor.
have hAm := @borel_regular_borel_measurable R X phi hm
  (derivation_measure_borel_regular hphi) A (closed_borel_set hA).
have hQ := (density_complement_zero_points_conclusions A hctx).2.2.2.1 hAm.
apply: (@measure_null_subset R X phi hm _
  (A `\` measure_density_complement_zero_points phi (@centered_closed_ball_relation R X) A) _ hQ).
move=> x [hx hnot]; split=> // hD; apply: hnot.
have hne : A !=set0 by exists x.
pose d := @MetricSetDistance.value R X A hne.
have hd : is_metric_set_distance A d := @MetricSetDistance.laws R X A hne.
exact (@closed_target_ratio_decay R X phi psi A d hd c delta lambda mu x
  hphi hpsi hA hc hl hdelta hmu hg hbound hnull hx hD).
Qed.

(** Source for [closed_null_target_upper_ratio_dichotomy]: direct
    countable C_n reduction for a closed numerator-null target
    in Federer 2.9.17, p. 162. Finite upper
    ratios belong to some uniform coefficient/radius locus;
    the complement-density argument gives zero there outside
    a countable union of null exceptional sets. *)
Lemma closed_null_target_upper_ratio_dichotomy (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop)
    (T : set X) (lambda mu : R) :
  is_measure_derivation_context phi V0 -> is_measure psi -> closed T ->
  (0<lambda)%R -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  psi T=0 -> measure_almost_everywhere_on phi T (has_zero_or_infinite_upper_ball_ratio psi phi).
Proof.
move=> hc0 hpsi hT hl hmu hg hnull.
have hphi := derivation_context_measure hc0; have hm := derivation_measure_law hphi.
pose C n := T `&` natural_centered_ball_ratio_locus psi phi n.
have hCclosed n : closed (C n).
  exact (@closed_target_ball_ratio_locus R X psi phi T
    (n.+1)%:R (((n.+1)%:R)^-1)%R hphi hpsi hT (ltac:(by rewrite ltr0n))).
have hCnull n : psi (C n)=0.
  exact (@measure_null_subset R X psi hpsi (C n) T (fun _ h => h.1) hnull).
have hCzero n : phi (C n `\` [set x | centered_ball_ratio_upper_limit psi phi x=0])=0.
  apply: (@closed_uniform_bound_ratio_zero R X phi psi V0 (C n)
    (n.+1)%:R (((n.+1)%:R)^-1)%R lambda mu hc0 hpsi (hCclosed n)
    (ltac:(by rewrite ler0n)) (ltac:(by rewrite invr_gt0 ltr0n)) hl hmu hg).
  - by move=> z [_ hz].
  - exact: hCnull n.
have hbad : phi (\bigcup_n (C n `\` [set x | centered_ball_ratio_upper_limit psi phi x=0]))=0.
  apply: (@measure_null_countable_union R X nat phi hm setT _ (countableP _)).
  by move=> n _; exact: hCzero n.
apply: (@measure_null_subset R X phi hm _ _ _ hbad).
move=> x [hx hn].
have hfinite : centered_ball_ratio_upper_limit psi phi x< +oo.
  rewrite ltNge leye_eq; apply/negP=> /eqP he; apply: hn; by right.
have hP := @strict_fivefold_growth_no_null_balls R X phi lambda mu hm hmu hg x.
have [n hnloc] := @finite_centered_ball_ratio_natural_cutoff R X psi phi x hphi hP hfinite.
exists n=> //; split; first by split.
move=> hz; apply: hn; by left.
Qed.

(** Source for [federer_2_9_17]: complete theorem of Federer
    2.9.17, p. 162, with the section's standing
    class-M reference and existing Vitali relation. The growth
    coefficient is finite, mu is positive, psi only measures
    X, and T is reference-measurable with psi(T)=0. The
    literal upper positive-radius ratio equals zero or infinity
    reference-almost everywhere on T. Closed inner approximation
    implements the printed reduction citing 2.2.3. Positivity
    of every ball and lambda>1 at any point are derived,
    not added hypotheses; the empty space is included. *)
Theorem federer_2_9_17 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop)
    (T : set X) (lambda mu : R) :
  is_measure_derivation_context phi V0 -> is_measure psi -> (0<mu)%R ->
  has_uniform_fivefold_ball_growth phi setT mu lambda ->
  measure_measurable phi T -> psi T=0 ->
  measure_almost_everywhere_on phi T (has_zero_or_infinite_upper_ball_ratio psi phi).
Proof.
move=> hc0 hpsi hmu hg hT hnull.
have hphi := derivation_context_measure hc0; have hm := derivation_measure_law hphi.
case: (pselect (exists x : X, True))=> [[x0 _]|hempty].
- have hlambda := @strict_fivefold_growth_coefficient_gt_one R X phi lambda mu hphi hmu hg x0.
  have hl : (0<lambda)%R := lt_trans ltr01 hlambda.
  have [C [hC hcover]] := @derivation_measurable_closed_almost_cover R X phi T hphi hT.
  have hCbad j : phi (C j `\` has_zero_or_infinite_upper_ball_ratio psi phi)=0.
    apply: (@closed_null_target_upper_ratio_dichotomy R X phi psi V0 (C j) lambda mu
      hc0 hpsi (hC j).1 hl hmu hg).
    exact (@measure_null_subset R X psi hpsi (C j) T (hC j).2 hnull).
  have hbad : phi (\bigcup_j (C j `\` has_zero_or_infinite_upper_ball_ratio psi phi))=0.
    apply: (@measure_null_countable_union R X (nat*nat)%type phi hm setT _ (countableP _)).
    by move=> j _; exact: hCbad j.
  have hunion := measure_null_union hm hcover hbad.
  apply: (@measure_null_subset R X phi hm _ _ _ hunion).
  move=> x [hx hn]; case: (pselect ((\bigcup_j C j) x))=> [[j _ hj]|hno].
  + right; exists j=> //; by split.
  + left; by split.
- have he : T `\` has_zero_or_infinite_upper_ball_ratio psi phi=set0.
    apply/seteqP; split=> x; last by move=> [].
    move=> _; apply: hempty; by exists x.
  by rewrite /measure_almost_everywhere_on he; exact: measure_empty hm.
Qed.

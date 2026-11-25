(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP MeasureDerivationContext
  MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws CoveringRelationUP CoveringRelationFineness
  CenteredBallRelations CenteredBallFineness DiametricRegularityUP DiameterWeightLaws
  WeightedEnlargements BallEnlargementBound EnlargementAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [has_uniform_fivefold_ball_growth]: supporting
    uniform cutoff form of the first alternative in Federer
    2.9.15, p. 160. Countably many target pieces permit
    fixed finite growth and radius cutoffs. The strict mass
    inequality itself excludes null balls on the target. *)
Definition has_uniform_fivefold_ball_growth (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) (d lambda : R) :=
  forall a, A a -> forall r : R, (0<r)%R -> (r<d)%R ->
    phi (metric_closed_ball a (5*r)%R)<lambda%:E*phi (metric_closed_ball a r).

(** Source for [centered_uniform_growth_subrelation_adequate]:
    supporting expansion of the application of 2.8.17 in
    Federer 2.9.15, p. 160. For one uniform growth piece,
    apply the diameter-enlargement estimate and 2.8.7 directly
    to the small positive-radius centered members of C(A).
    This local use respects the positivity correction to
    2.8.17 (erratum p. 3, book p. 151 line 24),
    without imposing positivity on balls centered outside A.
    Singleton balls are retained through radius representation. *)
Theorem centered_uniform_growth_subrelation_adequate (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (C : X -> set X -> Prop) (A : set X) (d lambda : R) :
  is_derivation_measure phi ->
  (forall x S, C x S -> centered_closed_ball_relation x S) ->
  (forall x, A x -> covering_relation_fine_at C x) ->
  (0<d)%R -> (1<lambda)%R -> has_uniform_fivefold_ball_growth phi A d lambda ->
  family_is_measure_adequate phi (covering_relation_image C A) A.
Proof.
move=> hphi hC hf hd hl hg; have hm := derivation_measure_law hphi.
pose F0 := covering_relation_image C A.
pose F := localized_centered_ball_family F0 A setT d.
have hFF0 : F `<=` F0 by move=> S [hS _].
have hballs S : F S -> exists a r, A a /\ (0<r<d)%R /\ S=metric_closed_ball a r.
  by move=> [_ [_ h]].
have hbounded S : F S -> metric_set_bounded S.
  move=> hS; have [a [r [_ [/andP [hr _] ->]]]] := hballs S hS.
  exact: covering_closed_ball_bounded (ltW hr).
have hc : is_covering_theory_context F phi.
  constructor.
  - exact hm.
  - move=> S hS; have [a [r [_ [_ ->]]]] := hballs S hS; exact: metric_closed_ball_closed.
  - exact: borel_regular_open_measurable (derivation_measure_borel_regular hphi).
  - exact: derivation_measure_bounded_finite hphi.
have [w hw] := @real_diameter_weight_exists R X F hbounded.
have hwn := @diameter_weight_nonnegative R X F w hw.
have hwb : exists b, forall S, F S -> (w S<=b)%R.
  exists (d+d)%R=> S hS.
  have [a [r [_ [/andP [hr hrd] hSr]]]] := hballs S hS.
  have hB : F (metric_closed_ball a r) by rewrite -hSr.
  rewrite hSr; apply: le_trans (@diameter_weight_ball_bound R X F w hw a r hB (ltW hr)) _.
  exact: lerD (ltW hrd) (ltW hrd).
have hhat S : F S -> phi (weighted_enlargement F w 2%R S)<lambda%:E*phi S.
  move=> hS; have [a [r [ha [/andP [hr hrd] hSr]]]] := hballs S hS.
  have hB : F (metric_closed_ball a r) by rewrite -hSr.
  have hinc := @diameter_enlargement_ball_bound R X F w 2%R hw
    (ltac:(by rewrite ler0n)) a r hB (ltW hr).
  have he : ((1+2*2)*r=5*r)%R by lra.
  rewrite he in hinc; rewrite hSr.
  exact: le_lt_trans (@measure_mono R X phi hm _ _ hinc) (hg a ha r hr hrd).
have hrad := @fine_centered_relation_small_radii R X C A hC hf.
have hFfine : family_covers_finely F A.
  move=> a ha e he.
  have hcap : (0<Num.min d e)%R by rewrite lt_min hd he.
  have [r [/andP [hr hrcap] hF0]] := hrad a ha (Num.min d e) hcap.
  have hrd : (r<d)%R.
    apply: lt_le_trans hrcap _; by rewrite ge_min lexx.
  have hre : (r<e)%R.
    apply: lt_le_trans hrcap _; by rewrite ge_min lexx orbT.
  exists (metric_closed_ball a r); split.
  - split=> //; split; first by move=> x _.
    exists a,r; split=> //; split=> //; by apply/andP; split.
  - split; first by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
    move=> x hx; exact: le_lt_trans hx hre.
have hadeq := @enlargement_control_adequacy R X F phi w 2%R lambda A hc
  hwn hwb (ltac:(by rewrite ltr1n)) hl hhat hFfine.
exact: (@adequate_family_mono_family R X phi F F0 A hFF0 hadeq).
Qed.

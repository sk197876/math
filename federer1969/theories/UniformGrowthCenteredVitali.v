(** Federer (1969), 3.3.4, p. 291: actual
    uniform strict fivefold growth supplies the
    centred-ball Vitali relation needed by 2.9.17.
    Expand the direct 2.8.17 covering argument;
    do not require an existing Vitali relation
    in order to prove this one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureDerivationContext CoveringFamilyUP
  CoveringRelationUP CenteredBallRelations CenteredBallFineness
  MetricClosedBalls TopologicalBorel UniformBallGrowthAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_fivefold_growth_centered_vitali]:
    supporting the application of 2.9.17 in
    Federer 3.3.4, p. 291. Actual strict
    uniform growth at every centre and the
    class-M laws give adequate fine subrelations
    by the already proved enlargement theorem. *)
Theorem uniform_fivefold_growth_centered_vitali (R:realType) (X:metricType R)
    (phi:set X->\bar R) (delta lambda:R):
  is_derivation_measure phi ->0<delta ->1<lambda ->
  has_uniform_fivefold_ball_growth phi setT delta lambda ->
  is_vitali_relation phi (@centered_closed_ball_relation R X).
Proof.
move=>hPhi hd hl hGrowth; constructor.
- exact:centered_closed_balls_covering.
- move=>S [x [_ [r [_ ->]]]]; apply:closed_borel_set; exact:metric_closed_ball_closed.
- exact:centered_closed_balls_fine.
- move=>C Z hC hFine.
  have hGZ:has_uniform_fivefold_ball_growth phi Z delta lambda.
    move=>x _ r hr hrd; exact:hGrowth x I r hr hrd.
  have hAdequate:=@centered_uniform_growth_subrelation_adequate R X phi C Z delta lambda
    hPhi hC hFine hd hl hGZ.
  have [G hG]:=hAdequate setT openT.
  exists G; split; first exact:adequate_selection_members hG.
  split; first exact:adequate_selection_countable hG.
  split; first exact:adequate_selection_disjoint hG.
  by have:=adequate_selection_remainder hG; rewrite setTI.
Qed.

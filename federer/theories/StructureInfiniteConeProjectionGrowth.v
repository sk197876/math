(** Federer (1969), 3.3.9, pp. 295–296: the original cone
    hypothesis gives actual infinite centered upper growth after projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructurePlaneGrowth StructureProjectionKernel StructureInfiniteConeWitness
  StructureProjectedConeBallCost StructureCenteredUpperInfinite EuclideanBallVolume
  EuclideanClosedBallVolume EuclideanNoncenteredVitali EuclideanLebesgueDimensions EuclideanApproximateContext
  MeasureDerivationContext MeasureUP MetricClosedBalls NullBallLocus TopologicalBorel
  MeasureRestriction MeasurePushforward CoveringRelationLimits CenteredBallRelations MeasureDerivates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_infinite_cone_projected_upper]: the
    infinite ball-quotient upper limit on p. 296 in Federer 3.3.9.
    Actual cones at simultaneous positive real scales yield actual
    projected closed balls; the exact positive alpha(m) cancels.
    All admissible natural degrees, including zero, are retained.
    No ordinary infinite derivative or image measurability is assumed. *)
Theorem structure_infinite_cone_projected_upper (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (psi:set (inner_metric_space (@euclidean_inner_productP R m))->\bar R)
    (x:inner_metric_space (@euclidean_inner_productP R n)):
  is_measure phi ->is_derivation_measure psi ->
  (forall S,borel_set S ->psi S=measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A) S) ->
  structure_plane_infinite_growth m phi A x (structure_projection_kernel hmn p) ->
  covering_upper_limit (@centered_closed_ball_relation R
      (inner_metric_space (@euclidean_inner_productP R m)))
    (measure_ratio_function psi (@euclidean_lebesgue_measure R m))
    (euclidean_projection_linear p x)=+oo%E.
Proof.
move=>hPhi hPsi hValue hGrowth.
have hReference:=derivation_context_measure (euclidean_approximate_context R m).
have hNotNull:~measure_null_ball_points (@euclidean_lebesgue_measure R m) (euclidean_projection_linear p x).
  move=>[r [hr hZero]]; have hPositive:=@euclidean_closed_ball_positive R m
    (euclidean_projection_linear p x) r hr.
  by rewrite hZero ltxx in hPositive.
apply:(@structure_centered_upper_infinite R
  (inner_metric_space (@euclidean_inner_productP R m))
  (@euclidean_lebesgue_measure R m) psi (euclidean_projection_linear p x) hReference hNotNull)=>d b hd.
have hDelta:0<d/4 by rewrite divr_gt0 // ltr0n.
pose c:=Num.max b 0+1.
have hbMax:b<=Num.max b 0 by rewrite le_max lexx.
have hMax0:0<=Num.max b 0 by rewrite le_max lexx orbT.
have hc:0<c by rewrite /c; nra.
have hbc:b<c by rewrite /c; nra.
pose alpha:=euclidean_unit_ball_volume R m.
have hAlpha:0<alpha:=(euclidean_unit_ball_volumeE R m).2.
have [r [s [/andP [hr hrd] [/andP [hs hs1] hCost]]]]:=
  @structure_infinite_cone_cost_witness R n m hmn phi A p x (d/4) 1 (c*alpha)
    hGrowth hDelta ltr01.
have hRho:0<r*s by rewrite mulr_gt0.
have hRhoD:r*s<d.
  have hScale:r*s<r by rewrite -{2}[r]mulr1 ltr_pM2l.
  have hDeltaD:d/4<d by nra.
  exact:lt_trans hScale (lt_trans hrd hDeltaD).
have hBall:=@structure_projected_cone_ball_cost R n m hmn phi A p psi x r s
  hPhi (derivation_measure_law hPsi) hValue hr hs.
have hLarge:=lt_le_trans hCost hBall.
have hC:(c%:E<psi (metric_closed_ball (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m)) (r*s))/
    euclidean_lebesgue_measure m (metric_closed_ball (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m)) (r*s)))%E.
  move:hLarge; rewrite [c*alpha]mulrC EFinM.
  by rewrite lte_pmul2l ?fin_numE ?lte_fin.
exists (r*s); split; first by apply/andP; split.
apply:lt_trans _ hC; by rewrite lte_fin.
Qed.

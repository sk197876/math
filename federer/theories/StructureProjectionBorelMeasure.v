(** Federer (1969), 3.3.7, p. 294: the original restricted
    projection measure makes every Borel target set measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureFiniteClosure MeasurableBorelFamily
  MeasureRestriction MeasurePushforward PushforwardMeasurableSets TopologicalBorel
  ContinuousBorelPreimages EuclideanInnerProduct InnerMetric EuclideanProjectionSpace StructureConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_closed_measurable_borel]: supporting the
    Borel-infimum measure in Federer 3.3.7, p. 294. The standing
    closed-set measurability from 3.3.1, p. 287, gives open-set
    measurability by complements and all Borel sets by 2.2.1, p. 60.
    No regularity or local-finiteness premise is added. *)
Theorem structure_closed_measurable_borel (R:realType) (X:topologicalType)
    (phi:set X-> \bar R):
  is_measure phi ->(forall S,closed S ->measure_measurable phi S) ->
  forall B,borel_set B ->measure_measurable phi B.
Proof.
move=>hPhi hClosed.
apply:(@open_measurable_implies_borel_measurable R X phi hPhi)=>U hU.
have hComplement:=hClosed (~` U) (open_closedC hU).
have hMeas:=measure_measurable_complement hComplement.
by rewrite setCK in hMeas.
Qed.

(** Source for [structure_projection_pushforward_borel_measurable]:
    supporting Borel regularity of the actual psi in Federer 3.3.7,
    p. 294. The original projection is continuous, and restriction
    to arbitrary original A preserves measurability of every original
    measurable set. No measurability of A or p(A) is required. *)
Theorem structure_projection_pushforward_borel_measurable (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->
  forall B:set (inner_metric_space (@euclidean_inner_productP R m)),borel_set B ->
    measure_measurable (measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A)) B.
Proof.
move=>hPhi B hB.
pose f:inner_metric_space (@euclidean_inner_productP R n)->
    inner_metric_space (@euclidean_inner_productP R m):=euclidean_projection_linear p.
have hPreimage:@borel_set
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] (f @^-1` B).
  exact (@continuous_borel_preimage
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    f (@euclidean_projection_continuous R n m p) B hB).
have hMeas:=@structure_closed_measurable_borel R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
  phi hPhi.1 hPhi.2 (f @^-1` B) hPreimage.
apply:(@pushforward_measurable_from_preimage R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (measure_restrict phi A) f B).
exact:(@measure_restrict_measurable R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  phi A (f @^-1` B) hMeas).
Qed.

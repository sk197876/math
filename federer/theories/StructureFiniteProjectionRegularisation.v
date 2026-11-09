(** Federer (1969), 3.3.9, pp. 295–296: actual finite
    Borel regularisation of the original restricted pushforward. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureProjectionBorelMeasure StructureImageRegularisationMass
  StructureEuclideanFiniteRadon MeasureUP MeasureBasic MeasureRestriction MeasurePushforward
  MeasureDerivationContext BorelRegularisationUP BorelRegularisation BorelRegularMeasureUP
  RadonMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_finite_projection_regularisation]: the
    actual Radon measure psi in Federer 3.3.9, pp. 295–296.
    Its total mass is the original finite phi(A), without source
    measurability, purity or boundedness. Borel-set values equal
    those of the original restricted pushforward. Derive every
    class-M and Radon premise; the regularisation stays local. *)
Theorem structure_finite_projection_regularisation (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->(phi A< +oo)%E ->
  exists psi:set (inner_metric_space (@euclidean_inner_productP R m))->\bar R,
    @is_borel_regularisation R
      [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
      (measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A)) psi /\
    is_derivation_measure psi /\
    @is_radon_measure R [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] psi /\
    psi setT=phi A /\
    forall S,borel_set S ->psi S=measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A) S.
Proof.
move=>hStructure hFinite.
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose f:inner_metric_space (@euclidean_inner_productP R n)->Y:=euclidean_projection_linear p.
pose mu:set Y->\bar R:=measure_pushforward f (measure_restrict phi A).
have hMu:is_measure mu:=measure_pushforward_is_measure f (measure_restrict_is_measure hStructure.1 A).
pose psi:=@borel_regularisation R [the topologicalType of Y] mu.
have hReg:@is_borel_regularisation R [the topologicalType of Y] mu psi:=borel_regularisation_laws mu.
have hPsi:is_measure psi:=borel_regularised_measure_is_measure hMu.
have hBorel S:borel_set S ->measure_measurable mu S.
  exact:(@structure_projection_pushforward_borel_measurable R n m phi A p hStructure S).
have hRegular:@is_borel_regular_measure R [the topologicalType of Y] psi:=
  borel_regularised_measure_borel_regular hMu hBorel.
have hValue S:borel_set S ->psi S=mu S.
  move=>hS; rewrite /psi; exact:(@borel_regularised_measure_borel_value R
    [the topologicalType of Y] mu hMu S hS).
have hTotal:psi setT=phi A.
  rewrite (hValue setT (open_borel_set (@openT [the topologicalType of Y]))).
  by rewrite /mu /measure_pushforward /measure_restrict preimage_setT setIT.
have hTotalFinite:(psi setT< +oo)%E by rewrite hTotal.
have hClass:is_derivation_measure psi.
  constructor; [exact:hPsi|exact:hRegular|].
  move=>S _; apply:le_lt_trans _ hTotalFinite.
  exact:(@measure_mono R _ psi hPsi S setT (subsetT S)).
have hRadon:=@structure_euclidean_finite_borel_radon R m psi hPsi hRegular hTotalFinite.
exists psi; split; first exact:hReg.
split; first exact:hClass.
split; first exact:hRadon.
split; first exact:hTotal.
exact:hValue.
Qed.

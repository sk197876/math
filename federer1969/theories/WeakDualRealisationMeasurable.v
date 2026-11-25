(** Federer (1969), 4.1.5, p. 349: the
    original weakly measurable representing field can
    be expressed in the actual abstract dual.
    Weak continuity of the exact identification
    transports measurability without changing evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP VectorDaniellHypotheses WeakDualRealisationUP WeakDualRealisationContinuity
  OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP PartialFunctionBasic MeasureUP
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weak_dual_realisation_measurable]: weak
    measurability of the actual Y* density in
    Federer 4.1.5, p. 349, transported by the
    proved weakly continuous identification. *)
Theorem weak_dual_realisation_measurable (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (J:weak_dual_space hNY->D) (hJ:is_weak_dual_realisation ed DN J)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (k:X->weak_dual_space hNY):
  is_measure_measurable_function mu (partial_function_total k) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(J (k x):open_family_topological_space hO.1))).
Proof.
move=>hk.
exact:(measurable_total_borel_postcomposition hm hk
  (continuous_borel_function (@weak_dual_realisation_continuous R Y NY hNY D ed DN J hJ O hO))).
Qed.

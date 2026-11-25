(** Federer (1969), 4.1.1, p. 346: weakly
    measurable dual fields with locally integrable
    norm and their distribution integral. These
    are independent specifications; existence of
    the continuous distribution is proved later. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_locally_integrable_weak_dual_field]: the
    original weak measurability and finite local
    norm integral in Federer 4.1.1, p. 346.
    Compact-set integrals use zero extension. *)
Record is_locally_integrable_weak_dual_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (YD:lmodType R)
    (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (xi:X->YD):Prop:={
  (** Source for [integrable_dual_field_weak_measurable]:
      measurability into the original weak dual,
      Federer 4.1.1, p. 346. *)
  integrable_dual_field_weak_measurable:is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1)));
  (** Source for [integrable_dual_field_local_norm]: every
      compact K has a finite dual-norm integral,
      Federer 4.1.1, p. 346. *)
  integrable_dual_field_local_norm:forall K:smooth_compact_set hNX (fun _=>True),
    exists b:R,is_measure_integral mu (real_total_integrand
      (fun x=>if pselect (smooth_compact_carrier K x) then DN (xi x) else 0)) b%:E
}.

(** Source for [is_distribution_integral_action]: the
    original formula T(phi)=integral <phi,xi>,
    Federer 4.1.1, p. 346. This specification
    does not assume the continuity to be proved. *)
Definition is_distribution_integral_action (R:realType) (X:choiceType) (Y YD E:lmodType R)
    (mu:set X->\bar R) (ed:Hom YD (Hom Y R^o)) (xi:X->YD)
    (value:E->X->Y) (T:Hom E R^o):=
  forall f:E,is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (value f x))) (T f)%:E.

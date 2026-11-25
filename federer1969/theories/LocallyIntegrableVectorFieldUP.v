(** Federer (1969), 4.1.2, p. 347: the
    original measurable Banach-valued function has locally
    integrable norm. This specification retains the actual
    function and compact sets before convolution is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureIntegralUP SummableRealFunctionUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_locally_integrable_vector_field]: measurability
    and the original finite integral of the norm
    on every compact subset, Federer 4.1.2, p. 347.
    Separability and completeness remain separate target hypotheses. *)
Record is_locally_integrable_vector_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (f:X->Y):Prop:={
  (** Source for [locally_integrable_vector_measurable]: the
      original vector-valued function is measurable,
      Federer 4.1.2, p. 347. *)
  locally_integrable_vector_measurable:is_measure_measurable_function mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY)));
  (** Source for [locally_integrable_vector_compact_norm]: every
      original compact subset has a finite norm
      integral, Federer 4.1.2, p. 347. *)
  locally_integrable_vector_compact_norm:forall K:smooth_compact_set hNX (fun _=>True),
    exists b:R,is_measure_integral mu (real_total_integrand
      (fun x=>if pselect (smooth_compact_carrier K x) then NY (f x) else 0)) b%:E
}.

(** Federer (1969), 4.1.18, pp. 375–377:
    a measurable ambient field restricts measurably
    to the original open subspace measure. This
    is the trace-set law of 2.1.2 and
    the original open-preimage definition of 2.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import OpenSubspaceMeasure MeasureUP MeasureAlmostBasic
  PartialFunctionBasic PartialFunctionPreimages MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_total_measurable_pullback]:
    measurable restriction to the original U,
    supporting compact L1 field transport in
    Federer 4.1.18, pp. 375–377. No point
    in U is chosen. *)
Theorem open_subspace_total_measurable_pullback (R:realType)
    (X:pseudoMetricType R) (U:set X) (mu:set X->\bar R)
    (hm:is_measure mu) (Y:topologicalType) (f:X->Y):
  is_measure_measurable_function mu (partial_function_total f)->
  is_measure_measurable_function (@open_subspace_measure R X U mu)
    (partial_function_total (fun x:set_type U=>f (set_val x))).
Proof.
move=>hF;constructor.
- rewrite partial_function_total_domain.
  exact:measure_almost_everywhere_true (@open_subspace_measure_is_measure R X U mu hm).
- move=>O hO;rewrite !partial_function_total_preimage.
  have hAmbient:=@measurable_function_open_preimage R X Y mu
    (partial_function_total f) hF O hO.
  rewrite partial_function_total_preimage in hAmbient.
  exact:(@open_subspace_preimage_measurable R X U mu (f @^-1` O) hAmbient).
Qed.

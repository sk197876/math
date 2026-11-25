(** Federer (1969), 4.1.5, p. 350:
    the original compact continuous fields belong
    to the Radon vector L1 class. Open inverse
    images give measurability, target separability
    gives the original A(mu,Y) condition, and
    the compact norm integral is finite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses VectorDaniellRationalSpan
  FunctionLatticeUP CompactSupportFunctionUP CompactContinuousVectorFields
  MeasureUP MeasureAlmostBasic PartialFunctionBasic PartialFunctionPreimages MeasurableFunctionUP
  MeasurableNormedFunctionUP RadonMeasureUP RealIntegralFunctionalUP MeasureLpMembershipUP
  SeparableVectorLone TotalNormedLone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_vector_measurable]:
    the original continuous fields are measurable for
    the Radon measure, supporting Federer 4.1.5,
    p. 350. *)
Theorem compact_continuous_vector_measurable (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (w:X->Y):
  compact_continuous_vector_fields hNY w ->
  is_measure_measurable_function mu (partial_function_total (w:X->real_norm_metric_space hNY)).
Proof.
move=>hw; constructor.
- rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
- move=>V hV; rewrite partial_function_total_preimage.
  exact:(@radon_open_measurable R X mu hr (w @^-1` V)
    ((@continuousP X (real_norm_metric_space hNY) w).1 hw.1 V hV)).
Qed.

(** Source for [compact_continuous_vector_normed_measurable]:
    the original A(mu,Y) condition for the compact
    continuous fields, Federer 4.1.5, p. 350. *)
Theorem compact_continuous_vector_normed_measurable (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu) (w:X->Y):
  compact_continuous_vector_fields hNY w ->
  is_measurable_normed_function mu (partial_function_total (w:X->real_norm_metric_space hNY)).
Proof.
move=>hw; have[D hD]:=@rational_dense_subspace_exists R Y NY hNY hSep.
exact:(@measurable_separable_vector_total R X Y NY hNY D hD mu hm w
  (@compact_continuous_vector_measurable R X Y NY hNY mu hm hr w hw)).
Qed.

(** Source for [compact_continuous_vector_lone_member]:
    compact continuous fields have finite original
    L1 norm for the representing Radon measure,
    Federer 4.1.5, p. 350. *)
Theorem compact_continuous_vector_lone_member (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (F:(X->R)->R)
    (hF:is_real_integral_functional mu
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) F)
    (w:X->Y):
  compact_continuous_vector_fields hNY w ->
  is_measure_lp_function mu 1 (partial_function_total (w:X->real_norm_metric_space hNY)).
Proof.
move=>hw.
have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) (fun x=>NY (w x)).
  split; first exact:(@compact_continuous_vector_field_norm R X Y NY hNY w hw).
  move=>x; exact:(real_seminorm_nonnegative hNY.1 (w x)).
exact:(@total_normed_lone_from_norm_integral R X Y NY hNY mu hm w (F (fun x=>NY (w x)))
  (@compact_continuous_vector_normed_measurable R X Y NY hNY hSep mu hm hr w hw) (hF _ hPositive)).
Qed.

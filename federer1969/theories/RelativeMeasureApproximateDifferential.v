(** Federer (1969), 3.2.19, p. 256: a relative differential
    on a chart is the approximate differential on W when the omitted
    set has zero m-density and the two tangent cones agree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MetricDensities MetricDensityZero MetricDensityZeroUnions
  RestrictedApproximateTangent TangentConeUP RelativeDifferentialUP
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relative_representative_measure_approximation]: supporting
    representative step for ap Df(w)=D[f restricted psi_i(K_i)](w)
    in Federer 3.2.19, p. 256. Retain the original domain W
    as a partial graph and use local agreement only inside the actual
    differentiability neighbourhood of the relative representative. *)
Theorem relative_representative_measure_approximation (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (mu : set X -> \bar R) m
    (W E : set X) (f : X -> Y) a (d : partial_function X Y) :
  is_measure mu -> E `<=` W ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict mu (W `\` E))) a 0%E ->
  @has_relative_norm_differential R X Y NX NY hNX setT E f a d ->
  exists (D : Hom X Y) (U : set X) (g : X -> Y),
    has_norm_differential NX NY U g a D /\
    is_tangent_differential_restriction NX E a D d /\
    has_measure_approximate_differential NY hNX (measure_restrict mu W) m
      (partial_function_source_restrict W (partial_function_total f)) a D.
Proof.
move=> hm hEW hLoss [_ [U [g [D [hD [hAgree hGraph]]]]]].
pose M := real_norm_metric_space hNX.
pose nu := measure_restrict mu W.
pose fW := partial_function_source_restrict W (partial_function_total f).
pose S := partial_function_agreement fW
  (partial_function_source_restrict U (partial_function_total g)).
have hFullE : partial_function_graph (@metric_density R M m (measure_restrict nu (~` E))) a 0%E.
  rewrite /nu measure_restrict_intersection -setDE; exact hLoss.
have [r [hr hU]] := norm_differential_interior hD.
have hFull : partial_function_graph (@metric_density R M m (measure_restrict nu (~` S))) a 0%E.
  apply: (@metric_restricted_density_zero_local_mono R M m nu (~` S) (~` E) a
    (measure_restrict_is_measure hm W) _ hFullE).
  exists r; split=> // x hNear hNot hxE.
  have hxNear : NX (x-a)<r.
    change (is_true (NX (a-x)<r)) in hNear.
    by rewrite (real_seminorm_subtract hNX.1).
  have hxU : U x.
    have hh := hU (x-a) hxNear; by rewrite addrC subrK in hh.
  apply: hNot; exists (f x); split.
  - split; [exact: hEW x hxE|reflexivity].
  - split=> //; exact: esym (hAgree x hxE hxU).2.
exists D,U,g; split; first exact hD.
split; first exact hGraph.
exists U,g; by split.
Qed.

(** Source for [relative_differential_is_measure_approximate]: the
    exact partial differential identity in Federer 3.2.19, p. 256.
    The differential's domain is the approximate tangent plane, with no
    arbitrary off-plane values; uniqueness compares ambient representatives
    only on that cone. The cone equality is supplied by 3.2.17 and
    zero omitted density in the rectifiable-set theorem. *)
Theorem relative_differential_is_measure_approximate (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (W E : set X) (f : X -> Y) a
    (d : partial_function X Y) :
  is_measure mu -> E `<=` W ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict mu (W `\` E))) a 0%E ->
  measure_approximate_tangent_cone hNX (measure_restrict mu W) m a=norm_tangent_cone NX E a ->
  @has_relative_norm_differential R X Y NX NY hNX setT E f a d ->
  is_measure_approximate_differential NY hNX (measure_restrict mu W) m
    (partial_function_source_restrict W (partial_function_total f)) a d.
Proof.
move=> hm hEW hLoss hCone hRel.
have [D [U [g [hD [hGraph hApprox]]]]] := relative_representative_measure_approximation hm hEW hLoss hRel.
split; first by exists D.
move=> v y; split.
- move=> hvy; have [hv hDy] := (hGraph v y).1 hvy.
  split; first by rewrite hCone.
  exists D; by split.
- move=> [hv [L [hL hLy]]].
  have hEqual := @measure_approximate_linear_maps_agree_on_cone R X Y NX NY hNX hNY
    (measure_restrict mu W) m (partial_function_source_restrict W (partial_function_total f)) a D L
    (measure_restrict_is_measure hm W) hApprox hL v hv.
  apply: (hGraph v y).2; split; [by rewrite -hCone|exact: eq_trans hEqual hLy].
Qed.

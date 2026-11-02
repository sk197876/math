(** Federer (1969), 3.2.16, p. 253, used in 3.2.28,
    pp. 265–267: an actual ambient differential restricts
    to the approximate differential of its source restriction.
    The restricted measure has no mass outside the actual source. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureBasic MeasureRestriction MetricDensityZeroPowerMass
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ambient_differential_restricted_approximate_witness]:
    use the ambient differentiable map itself as representative,
    Federer 3.2.16, p. 253, in the area/coarea applications
    of 3.2.28, pp. 265–267. No global Lipschitz assumption
    or finite mass is required for this local fact. *)
Theorem ambient_differential_restricted_approximate_witness (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (phi:set X->\bar R) m (S:set X) (F:X->Y) a (D:Hom X Y):
  is_measure phi ->has_norm_differential NX NY (fun _=>True) F a D ->
  has_measure_approximate_differential NY hNX (measure_restrict phi S) m
    (partial_function_source_restrict S (partial_function_total F)) a D.
Proof.
move=>hPhi hD.
pose f:=partial_function_source_restrict S (partial_function_total F).
pose g:=partial_function_source_restrict (fun _=>True) (partial_function_total F).
have hAgreement:partial_function_agreement f g=S.
  apply/seteqP; split=>x.
  - by move=>[y [[hx _] _]].
  - move=>hx; exists (F x); by split; split.
pose nu:=measure_restrict phi S.
have hNu:is_measure nu:=measure_restrict_is_measure hPhi S.
have hZero:nu (~` S)=0%E.
  rewrite /nu /measure_restrict.
  have hEmpty:S `&` (~` S)=set0.
    apply/seteqP; split=>[x [hx hn]|x []]; exfalso; exact:hn hx.
  rewrite hEmpty; exact:measure_empty hPhi.
exists (fun _=>True),F; split; first exact hD.
change (partial_function_graph (@MetricDensities.metric_density R
  (real_norm_metric_space hNX) m (measure_restrict nu (~` partial_function_agreement f g))) a 0%E).
rewrite hAgreement.
exact:(@null_set_metric_density_zero R (real_norm_metric_space hNX) m nu (~` S) a hNu hZero).
Qed.

(** Source for [ambient_differential_restricted_approximate_graph]:
    the exact partial differential in Federer 3.2.16, p. 253,
    for the manifold maps of 3.2.28, pp. 265–267.
    Only the actual approximate tangent is the domain; an
    ambient derivative supplies no additional graph values. *)
Theorem ambient_differential_restricted_approximate_graph (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (phi:set X->\bar R) m (S:set X) (F:X->Y) a (D:Hom X Y):
  is_measure phi ->has_norm_differential NX NY (fun _=>True) F a D ->
  is_measure_approximate_differential NY hNX (measure_restrict phi S) m
    (partial_function_source_restrict S (partial_function_total F)) a
    (partial_function_source_restrict
      (measure_approximate_tangent_cone hNX (measure_restrict phi S) m a)
      (partial_function_total D)).
Proof.
move=>hPhi hD.
have hApprox:=@ambient_differential_restricted_approximate_witness R X Y NX NY hNX
  phi m S F a D hPhi hD.
have hNu:=measure_restrict_is_measure hPhi S.
split; first by exists D.
move=>v y; split.
- move=>[hv hDy]; split; first exact hv.
  exists D; by split.
- move=>[hv [E [hE hEy]]]; split; first exact hv.
  have hEqual:=@measure_approximate_linear_maps_agree_on_cone R X Y NX NY hNX hNY
    (measure_restrict phi S) m
    (partial_function_source_restrict S (partial_function_total F)) a D E hNu hApprox hE v hv.
  exact:eq_trans hEqual hEy.
Qed.

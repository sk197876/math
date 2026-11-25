(** Federer (1969), 3.2.33, p. 270: actual ordinary
    differentials on the original open source give approximate
    witnesses for its restricted measure, as in 3.2.16. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureBasic MeasureRestriction
  MetricDensities MetricDensityZeroPowerMass MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialUniqueness MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_restricted_measure_approximate]:
    supporting the actual approximate interpretation of the smooth
    example in Federer 3.2.33, p. 270. Use the original
    differentiable representative on W. Its agreement complement
    has zero restricted measure everywhere, so its density is zero.
    This statement needs no source measurability, density or
    local-finiteness premise. *)
Lemma norm_differential_restricted_measure_approximate (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (mu:set X->\bar R) (W:set X) m (F:X->Y) a (L:Hom X Y):
  is_measure mu ->has_norm_differential NX NY W F a L ->
  has_measure_approximate_differential NY hNX (measure_restrict mu W) m
    (partial_function_source_restrict W (partial_function_total F)) a L.
Proof.
move=>hm hD.
pose f:=partial_function_source_restrict W (partial_function_total F).
exists W,F; split; first exact hD.
have hNull:measure_restrict mu W (~` partial_function_agreement f f)=0%E.
  rewrite /measure_restrict.
  have hEmpty:W `&` ~` partial_function_agreement f f=set0.
    apply/seteqP; split=>x hx; last by case:hx.
    have hG:partial_function_graph f x (F x) by split; first exact hx.1; reflexivity.
    apply:hx.2; exists (F x); by split.
  by rewrite hEmpty (measure_empty hm).
exact:(@null_set_metric_density_zero R (real_norm_metric_space hNX) m (measure_restrict mu W)
  (~` partial_function_agreement f f) a (measure_restrict_is_measure hm W) hNull).
Qed.

(** Source for [full_cone_approximate_differential_total_graph]:
    on a full approximate tangent the differential of the smooth
    example in Federer 3.2.33, p. 270, is its actual
    entire linear map. The independent approximate graph law and
    proved uniqueness on the cone exclude arbitrary off-domain
    extensions. This supporting lemma introduces no chosen field. *)
Lemma full_cone_approximate_differential_total_graph (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) m (f:partial_function X Y) a (L:Hom X Y):
  is_measure mu ->has_measure_approximate_differential NY hNX mu m f a L ->
  measure_approximate_tangent_cone hNX mu m a=setT ->
  is_measure_approximate_differential NY hNX mu m f a (partial_function_total L).
Proof.
move=>hm hD hFull; split; first by exists L.
move=>v y; split.
- move=>hValue; split; first by rewrite hFull.
  exists L; by split.
- move=>[hv [D [hOther hValue]]].
  have hEq:=measure_approximate_linear_maps_agree_on_cone hNY hm hD hOther hv.
  change (L v=y); by rewrite hEq.
Qed.

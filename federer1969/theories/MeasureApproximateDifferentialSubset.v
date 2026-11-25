(** Federer (1969), 3.2.32, pp. 269–270: supporting
    preservation of the original approximate differential when
    applying 3.2.22 on measurable source restrictions. The
    cone restriction follows the full-density laws of 3.2.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureRestriction MetricDensities MetricDensityZeroUnions
  RestrictedApproximateTangent MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialUniqueness MeasureApproximateLinearModel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_approximate_representative_subset]: supporting
    source restriction in Federer 3.2.32, pp. 269–270.
    A differentiable representative whose disagreement has zero
    source-degree density on B has the same property on A
    whenever A is contained in B. Actual partial graphs and
    defining density denominators are retained. *)
Theorem measure_approximate_representative_subset (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (phi:set X->\bar R) m (A B:set X) (F:X->Y) a (D:Hom X Y):
  is_measure phi ->A `<=` B ->
  has_measure_approximate_differential NY hNX (measure_restrict phi B) m
    (partial_function_source_restrict B (partial_function_total F)) a D ->
  has_measure_approximate_differential NY hNX (measure_restrict phi A) m
    (partial_function_source_restrict A (partial_function_total F)) a D.
Proof.
move=>hPhi hAB [U [g [hD hZero]]].
pose fA:=partial_function_source_restrict A (partial_function_total F).
pose fB:=partial_function_source_restrict B (partial_function_total F).
pose gU:=partial_function_source_restrict U (partial_function_total g).
pose EA:=~` partial_function_agreement fA gU.
pose EB:=~` partial_function_agreement fB gU.
have hSub:(A `&` EA) `<=` (B `&` EB).
  move=>x [hx hNot]; split; first exact:hAB.
  move=>[y [[hBx hFy] hgy]]; apply:hNot.
  exists y; split; first by split.
  exact hgy.
exists U,g; split; first exact hD.
change (partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
  (measure_restrict (measure_restrict phi A) EA)) a 0).
change (partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
  (measure_restrict (measure_restrict phi B) EB)) a 0) in hZero.
rewrite !measure_restrict_intersection in hZero *.
exact (@metric_restricted_density_zero_subset R (real_norm_metric_space hNX) m phi
  (A `&` EA) (B `&` EB) a hPhi hSub hZero).
Qed.

(** Source for [measure_approximate_differential_subset_same_cone]:
    supporting unchanged intrinsic differential on source pieces
    in Federer 3.2.32, pp. 269–270. Once the actual cones
    agree, the original partial differential is also the restricted
    one. Linear representatives transfer to the smaller source,
    and uniqueness on the common cone proves both graph directions.
    There is no off-cone extension of the public differential. *)
Theorem measure_approximate_differential_subset_same_cone (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (phi:set X->\bar R) m (A B:set X) (F:X->Y) a (d:partial_function X Y):
  is_measure phi ->A `<=` B ->
  measure_approximate_tangent_cone hNX (measure_restrict phi A) m a=
    measure_approximate_tangent_cone hNX (measure_restrict phi B) m a ->
  is_measure_approximate_differential NY hNX (measure_restrict phi B) m
    (partial_function_source_restrict B (partial_function_total F)) a d ->
  is_measure_approximate_differential NY hNX (measure_restrict phi A) m
    (partial_function_source_restrict A (partial_function_total F)) a d.
Proof.
move=>hPhi hAB hCone hB.
have hPhiB:=measure_restrict_is_measure hPhi B.
have hPhiA:=measure_restrict_is_measure hPhi A.
have [D [hDB hModel]]:=@measure_approximate_differential_linear_model R X Y NX NY hNX hNY
  (measure_restrict phi B) m (partial_function_source_restrict B (partial_function_total F)) a d hPhiB hB.
have hDA:=@measure_approximate_representative_subset R X Y NX NY hNX phi m A B F a D hPhi hAB hDB.
split; first by exists D.
move=>v y; split.
- move=>hvy; have [hv _]:=(hB.2 v y).1 hvy.
  split; first by rewrite hCone.
  exists D; split; first exact hDA; exact:hModel.
- move=>[hv [E [hE hEy]]].
  have hEqual:=@measure_approximate_linear_maps_agree_on_cone R X Y NX NY hNX hNY
    (measure_restrict phi A) m (partial_function_source_restrict A (partial_function_total F))
    a D E hPhiA hDA hE v hv.
  apply:(hB.2 v y).2; split; first by rewrite -hCone.
  exists D; split; first exact hDB; exact (eq_trans hEqual hEy).
Qed.

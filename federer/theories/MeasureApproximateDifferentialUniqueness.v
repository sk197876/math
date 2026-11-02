(** Federer (1969), 3.2.16, p. 253:
    the approximate differential is determined by f
    on its approximate tangent cone. Combine the
    density-full agreement sets and use the tangent
    differential agreement theorem of 3.1.22. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormVanishingTangent
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionality
  MeasureUP MeasureRestriction MetricDensities MetricDensityZeroUnions
  TangentConeUP TangentConeBasic MeasureApproximateTangentUP MeasureApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_approximate_linear_maps_agree_on_cone]:
    the uniqueness assertion preceding ap Df(a)
    in Federer 3.2.16, p. 253. Ambient
    linear representatives are compared only on the
    approximate tangent cone; no full-rank or
    positive-density assumption is added. *)
Theorem measure_approximate_linear_maps_agree_on_cone (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (f : partial_function X Y) a (D E : Hom X Y) :
  is_measure phi ->
  has_measure_approximate_differential NY hNX phi m f a D ->
  has_measure_approximate_differential NY hNX phi m f a E ->
  forall v, measure_approximate_tangent_cone hNX phi m a v -> D v=E v.
Proof.
move=> hm [U [g [hD hFull]]] [V [h [hE hFull']]] v hv.
pose M := real_norm_metric_space hNX.
pose S := partial_function_agreement f
  (partial_function_source_restrict U (partial_function_total g)).
pose T := partial_function_agreement f
  (partial_function_source_restrict V (partial_function_total h)).
have hST : partial_function_graph (@metric_density R M m
    (measure_restrict phi (~` (S `&` T)))) a 0.
  rewrite setCI.
  exact: (@metric_restricted_density_zero_union R M m phi (~` S) (~` T) a hm hFull hFull').
have hTan : norm_tangent_cone NX (S `&` T) a v := hv (S `&` T) hST.
have hcl := @norm_tangent_base_closure R X NX hNX (S `&` T) a v hTan.
have hAgree x : (S `&` T) x -> U x -> V x -> g x=h x.
  move=> [hxS hxT] hxU hxV.
  have [y [hfy [_ hgy]]] := hxS.
  have [z [hfz [_ hhz]]] := hxT.
  have hyz := partial_function_single_valued hfy hfz.
  exact: (eq_trans hgy (eq_trans hyz (esym hhz))).
exact: (@norm_differentials_agree_on_tangent R X Y NX NY hNX hNY U V (S `&` T)
  g h a D E hD hE hcl hAgree v hTan).
Qed.

(** Source for [measure_approximate_differential_unique]:
    uniqueness of the partial differential on the
    exact cone in Federer 3.2.16, p. 253.
    Its independent graph laws determine the object. *)
Theorem measure_approximate_differential_unique (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) a (d e : partial_function X Y) :
  is_measure_approximate_differential NY hNX phi m f a d ->
  is_measure_approximate_differential NY hNX phi m f a e -> d=e.
Proof.
move=> hd he; apply: partial_function_graph_extensionality=> v y; split=> hy.
- exact: (he.2 v y).2 ((hd.2 v y).1 hy).
- exact: (hd.2 v y).2 ((he.2 v y).1 hy).
Qed.

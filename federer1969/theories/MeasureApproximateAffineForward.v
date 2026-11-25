(** Federer (1969), 3.2.16, p. 253:
    a differentiable density-full representative
    gives the affine-remainder criterion. Keep the
    actual domain of f and use g(a) for eta,
    without assigning a value to f at a. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MetricDensities MetricDensityZero
  MeasureApproximateDifferentialUP MeasureApproximateAffineUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_differential_affine_criterion]:
    the forward implication of the affine
    characterization in Federer 3.2.16, p. 253.
    Every witnessing ambient differential retains
    its own affine value eta=g(a). *)
Theorem measure_approximate_differential_affine_criterion (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) (a : X) (D : Hom X Y) :
  is_measure phi -> has_measure_approximate_differential NY hNX phi m f a D ->
  exists eta, has_measure_approximate_affine_criterion NY hNX phi m f a eta D.
Proof.
move=> hm [U [g [hD hFull]]].
pose M := real_norm_metric_space hNX.
pose S := partial_function_agreement f
  (partial_function_source_restrict U (partial_function_total g)).
exists (g a); split; first exact: norm_differential_bounded hD.
move=> e he.
have [d [hd hError]] := norm_differential_remainder hD he.
apply: (@metric_restricted_density_zero_local_mono R M m phi
  (~` measure_affine_approximation_set NX NY f a (g a) D e) (~` S) a hm _ hFull).
exists d; split=> // x hdist hBad hxS.
have [y [hfy [hxU hgy]]] := hxS.
have hsmall : NX (x-a)<d.
  change (is_true (NX (a-x)<d)) in hdist.
  by rewrite (real_seminorm_subtract hNX.1).
have hshift : a+(x-a)=x by rewrite addrC subrK.
have hxU' : U (a+(x-a)) by rewrite hshift.
have hh := hError (x-a) hxU' hsmall; rewrite hshift in hh.
apply: hBad; exists y; split=> //.
by rewrite -hgy.
Qed.

(** Federer (1969), 3.2.16, p. 253,
    and erratum p. 5, line 32: at
    a positive atom the affine value is an
    actual value of f. This justifies adjoining
    the centre to the selected annular set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP MeasureUP
  MeasureApproximateAffineUP MetricDensityPositiveAtom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_affine_positive_atom_value]:
    the base-value condition needed when T
    is replaced by T union {a} in the
    erratum to Federer 3.2.16, p. 253
    line 32. A positive atom forces both
    actual domain membership and f(a)=eta. *)
Theorem measure_affine_positive_atom_value (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (f : partial_function X Y) a eta (D : Hom X Y) :
  is_measure phi -> (0<phi [set a])%E ->
  has_measure_approximate_affine_criterion NY hNX phi m f a eta D ->
  partial_function_graph f a eta.
Proof.
move=> hm hAtom [_ hcrit].
have hBad := hcrit 1 (@ltr01 R).
have hExclude := @metric_zero_density_excludes_positive_atom R
  (real_norm_metric_space hNX) m phi
  (~` measure_affine_approximation_set NX NY f a eta D 1) a hm hAtom hBad.
have hGood : measure_affine_approximation_set NX NY f a eta D 1 a.
  apply: contrapT=> hn; exact: hExclude hn.
have [y [hfy herr]] := hGood.
rewrite subrr linear0 subr0 (real_seminorm_zero hNX.1) mulr0 in herr.
have hz : NY (y-eta)=0.
  apply/eqP; rewrite eq_le herr (real_seminorm_nonnegative hNY.1); reflexivity.
have hye : y=eta.
  have heq := hNY.2 (y-eta) hz; apply/eqP; by rewrite -subr_eq0 heq eqxx.
by rewrite -hye.
Qed.

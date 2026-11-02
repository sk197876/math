(** Federer (1969), 3.2.16, p. 253,
    corrected by erratum p. 5, line 32:
    the annular set is density-full after the
    centre is adjoined precisely at a positive atom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP
  MeasureRestriction MetricDensities MetricDensityZeroPowerMass MetricDensityZeroUnions
  GeometricErrorBudget RecurrentContraction NormAnnularSetUP NormAnnularOmissionBound
  MetricDensityAnnularRadii ShrinkingRadiusSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_annular_omission_zero_density]:
    vanishing m-density of the omitted noncentral
    points, Federer 3.2.16, p. 253.
    The proof controls a full tail, so
    it covers every sufficiently small radius. *)
Theorem norm_annular_omission_zero_density (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (mu : set X -> \bar R) m
    (S : nat -> set X) a (rho : nat -> R) (T : set X) :
  is_measure mu ->
  is_shrinking_radius_selection
    (@metric_density_annular_radius_property R (real_norm_metric_space hNX) mu m S a) rho ->
  is_norm_annular_set NX S a rho T ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict mu ((~` T) `\` [set a]))) a 0%E.
Proof.
move=> hm hR hT.
apply: (@small_power_mass_metric_zero_density R (real_norm_metric_space hNX) m mu ((~` T) `\` [set a]) a hm _)=> e he.
have hq0 : 0<(2:R)^-1 by rewrite invr_gt0 ltr0n.
have hq1 : (2:R)^-1<1 by rewrite invf_lt1 // ltr1n.
have hq : 0<(2:R)^-1<1 by apply/andP; split.
have [J hJ] := @geometric_contraction_small R ((2:R)^-1) 1 e hq ler01 he.
have htail : geometric_error_tail (2:R) J<=e.
  rewrite /geometric_error_tail divff ?pnatr_eq0 // mul1r.
  rewrite mulr1 in hJ; exact: ltW hJ.
exists (rho J); split; first exact: shrinking_radius_positive hR J.
move=> r hr.
apply: (le_trans (norm_annular_omission_mass_bound hm hR hT hr) _).
rewrite lee_fin [e*r^+m]mulrC.
exact: (ler_wpM2l (exprn_ge0 m (ltW (andP hr).1)) htail).
Qed.

(** Source for [norm_annular_corrected_set]:
    T, or T union {a} when phi{a}>0,
    in the erratum to Federer 3.2.16,
    p. 253 line 32. No value at a
    is imposed when the singleton is null. *)
Definition norm_annular_corrected_set (R : realType) (X : Type)
    (mu : set X -> \bar R) (a : X) (T : set X) : set X :=
  T `|` [set x | x=a /\ (0<mu [set a])%E].

(** Source for [norm_annular_corrected_full_density]:
    the density-fullness conclusion of the corrected
    annular proof, Federer 3.2.16, p. 253.
    A nonpositive atom is null by nonnegativity;
    a positive atom is included in the set. *)
Theorem norm_annular_corrected_full_density (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (mu : set X -> \bar R) m
    (S : nat -> set X) a (rho : nat -> R) (T : set X) :
  is_measure mu ->
  is_shrinking_radius_selection
    (@metric_density_annular_radius_property R (real_norm_metric_space hNX) mu m S a) rho ->
  is_norm_annular_set NX S a rho T ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict mu (~` norm_annular_corrected_set mu a T))) a 0%E.
Proof.
move=> hm hR hT.
have hP := norm_annular_omission_zero_density hm hR hT.
case: (boolP (0<mu [set a])%E)=> hAtom.
- apply: (@metric_restricted_density_zero_subset R (real_norm_metric_space hNX) m mu
    (~` norm_annular_corrected_set mu a T) ((~` T) `\` [set a]) a hm _ hP).
  move=> x hx; split.
  + move=> ht; apply: hx; by left.
  + move=> heq; apply: hx; right; by split.
- have hNull : mu [set a]=0%E.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt hAtom; reflexivity.
  have hA := @null_set_metric_density_zero R (real_norm_metric_space hNX)
    m mu [set a] a hm hNull.
  have hUnion := @metric_restricted_density_zero_union R (real_norm_metric_space hNX) m mu
    ((~` T) `\` [set a]) [set a] a hm hP hA.
  apply: (@metric_restricted_density_zero_subset R (real_norm_metric_space hNX) m mu
    (~` norm_annular_corrected_set mu a T) (((~` T) `\` [set a]) `|` [set a]) a hm _ hUnion).
  move=> x hx; case: (pselect (x=a))=> heq; first by right.
  left; split=> // ht; apply: hx; by left.
Qed.

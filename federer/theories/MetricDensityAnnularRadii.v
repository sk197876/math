(** Federer (1969), 3.2.16, p. 253:
    prove availability of the radius conditions,
    then invoke the opaque shrinking-radius laws.
    The erratum requires strict half-radius decrease. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureRestriction
  MetricClosedBalls MetricDensities MetricDensityZeroPowerMass
  GeometricErrorBudget ShrinkingRadiusSelectionUP ShrinkingRadiusSelectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_density_annular_radius_property]:
    the small-ball estimate defining delta_i,
    Federer 3.2.16, p. 253. Here i=n+1
    and the geometric budget is 2^(-i). *)
Definition metric_density_annular_radius_property (R : realType)
    (X : metricType R) (mu : set X -> \bar R) m
    (S : nat -> set X) (a : X) n (d : R) :=
  forall r : R, 0<r<=d ->
    (mu ((~` S n) `&` metric_closed_ball a r) <=
      (geometric_error_budget (2:R) n*r^+m)%R%:E)%E.

(** Source for [metric_density_annular_radii_exist]:
    the simultaneous choice of delta_i in
    Federer 3.2.16, p. 253, with
    delta_(i+1)<delta_i/2 as corrected by the erratum.
    No local finiteness of mu is required. *)
Theorem metric_density_annular_radii_exist (R : realType)
    (X : metricType R) (mu : set X -> \bar R) m
    (S : nat -> set X) (a : X) :
  is_measure mu ->
  (forall n, partial_function_graph
    (metric_density m (measure_restrict mu (~` S n))) a 0%E) ->
  exists rho, is_shrinking_radius_selection
    (metric_density_annular_radius_property mu m S a) rho.
Proof.
move=> hm hS.
have hSmall n : exists d : R, 0<d /\
    metric_density_annular_radius_property mu m S a n d.
  apply: (metric_zero_density_small_power_mass hm (hS n)).
  apply: geometric_error_budget_positive; by rewrite ltr0n.
have hDown n (r s : R) : 0<s<=r ->
    metric_density_annular_radius_property mu m S a n r ->
    metric_density_annular_radius_property mu m S a n s.
  move=> /andP [hs hsr] hr t /andP [ht hts].
  apply: hr; apply/andP; split=> //; exact: le_trans hts hsr.
exists (@ShrinkingRadiusSelection.value R _ hSmall hDown).
exact: ShrinkingRadiusSelection.laws.
Qed.

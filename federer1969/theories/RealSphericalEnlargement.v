(** Federer 2.10.19(3)-(5), p. 181: reuse the existing sealed
    degree-one spherical containing ball for every real power gauge.
    Its geometric laws suffice; no representation is opened. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology.
From Federer Require Import RealPower MetricRealPowerCost HausdorffMeasureUP
  HausdorffDiameterCost CaratheodoryWeakEnlargementUP WeakEnlargementRealPower
  SphericalEnlargementUP SphericalEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_spherical_enlargement_control]: supporting finite
    positive control for Federer 2.10.19(3)-(5), p. 181. Retain the
    existing degree-one geometric control and its real p-th power. *)
Definition real_spherical_enlargement_control (R : realType) (p : R) :=
  Order.max (spherical_enlargement_control R 1)
    (real_power (spherical_enlargement_control R 1) p).

(** Source for [real_spherical_enlargement_specification]: supporting
    containing-ball laws for the real-degree spherical assertions of
    Federer 2.10.19(3)-(5), p. 181. The ball is the already sealed
    degree-one enlargement. Its member, containment and diameter laws
    transfer to the real power cost, including zero-cost balls. *)
Theorem real_spherical_enlargement_specification (R : realType) (X : metricType R)
    (a p : R) : (0<=a)%R -> (0<=p)%R ->
    is_weak_caratheodory_enlargement (@is_positive_metric_closed_ball R X)
      (@metric_real_diameter_cost R X a p) (@spherical_enlargement R X 1)
      (@real_spherical_enlargement_control R p).
Proof.
move=> ha hp.
exact: (@weak_enlargement_transfer_real_power R X
  (@is_positive_metric_closed_ball R X) (@hausdorff_diameter_cost R X 1)
  (@spherical_enlargement R X 1) (spherical_enlargement_control R 1) a p
  (@spherical_enlargement_specification R X 1) ha hp).
Qed.

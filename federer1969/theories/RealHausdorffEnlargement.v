(** Federer 2.10.24, p. 188: transfer the existing sealed Hausdorff
    enlargement laws to every nonnegative real diameter power. No
    closed set, centre, radius or containing cover is chosen again. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower MetricRealPowerCost HausdorffDiameterCost CaratheodoryWeakEnlargementUP WeakEnlargementRealPower
  ClosedHausdorffEnlargementUP ClosedHausdorffEnlargement HausdorffGeneratorEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_enlargement_control]: supporting
    common control for the Hausdorff applications in Federer 2.10.24,
    p. 188. Take the maximum of the existing positive degree-one
    geometric control and its real power. *)
Definition real_hausdorff_enlargement_control (R : realType) (p : R) :=
  Order.max (closed_hausdorff_enlargement_control R 1)
    (real_power (closed_hausdorff_enlargement_control R 1) p).

(** Source for [real_closed_hausdorff_enlargement_specification]:
    supporting weak growth laws for the closed-generator connection
    in Federer 2.10.24, p. 188. The existing sealed enlargement and
    its geometric laws suffice for every nonnegative real degree,
    including unbounded generators and zero costs. *)
Theorem real_closed_hausdorff_enlargement_specification (R : realType)
    (X : metricType R) (a p : R) :
    (0<=a)%R -> (0<=p)%R ->
    is_weak_caratheodory_enlargement [set S : set X | closed S /\ S!=set0]
      (@metric_real_diameter_cost R X a p)
      (@closed_hausdorff_enlargement R X 1)
      (@real_hausdorff_enlargement_control R p).
Proof.
move=> ha hp.
exact: (@weak_enlargement_transfer_real_power R X
  [set S : set X | closed S /\ S!=set0] (@hausdorff_diameter_cost R X 1)
  (@closed_hausdorff_enlargement R X 1) (closed_hausdorff_enlargement_control R 1)
  a p (@closed_hausdorff_enlargement_specification R X 1) ha hp).
Qed.

(** Source for [real_hausdorff_generator_enlargement_specification]:
    supporting weak growth laws for the original nonempty generators
    in Federer 2.10.24, p. 188. Transfer the existing closure connection,
    keeping its opaque closed enlargement, zero diameters and infinities. *)
Theorem real_hausdorff_generator_enlargement_specification (R : realType)
    (X : metricType R) (a p : R) :
    (0<=a)%R -> (0<=p)%R ->
    is_weak_caratheodory_enlargement [set S : set X | S!=set0]
      (@metric_real_diameter_cost R X a p)
      (@hausdorff_generator_enlargement R X 1)
      (@real_hausdorff_enlargement_control R p).
Proof.
move=> ha hp.
exact: (@weak_enlargement_transfer_real_power R X
  [set S : set X | S!=set0] (@hausdorff_diameter_cost R X 1)
  (@hausdorff_generator_enlargement R X 1) (closed_hausdorff_enlargement_control R 1)
  a p (@hausdorff_generator_enlargement_laws R X 1) ha hp).
Qed.

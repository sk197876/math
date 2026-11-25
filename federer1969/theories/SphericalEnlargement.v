(** Public containing-ball interface supporting Federer (1969), 2.10.19, p.
    181 Expose only the weak growth and containment laws. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffDiameterCost CaratheodoryWeakEnlargementUP
  SphericalEnlargementUP SphericalEnlargementSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [spherical_enlargement]: public sealed containing ball for
    2.10.19(3)–(5), p. 181 No centre or radius choice is exposed. *)
Definition spherical_enlargement (R : realType) (X : metricType R) (m : nat) :=
  @SphericalEnlargement.value R X m.

(** Source for [spherical_enlargement_specification]: proved weak
    enlargement laws used for 2.10.19(3)–(5), p. 181 Zero-cost and
    zero-diameter balls are retained. *)
Lemma spherical_enlargement_specification (R : realType) (X : metricType R) (m : nat) :
  is_weak_caratheodory_enlargement (@is_positive_metric_closed_ball R X)
    (@hausdorff_diameter_cost R X m) (@spherical_enlargement R X m) (spherical_enlargement_control R m).
Proof. exact: SphericalEnlargement.laws. Qed.

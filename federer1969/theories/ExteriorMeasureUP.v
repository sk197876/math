(** Federer (1969), 2.10.3, pp. 171–172: specify the measure T^m by applying
    the abstract Caratheodory construction to all nonempty Euclidean sets
    and the normalized exterior-product diameter. The target degree is
    positive; degrees greater than ambient dimension remain permitted.
    Alternative open, compact and convex families are to be proved
    separately, not assumed by this specification. Source context and
    auxiliary conventions: ExteriorDiameterUP.v and ExteriorMeasureGauge.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  HausdorffLengthUP ExteriorMeasureGauge CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_exterior_diameter_measure]: direct
    Caratheodory specification of T^m in Federer
    2.10.3, p. 171. The gauge is given by actual
    exterior vectors and their norms, rather than
    a placeholder scalar diameter power. *)
Definition is_exterior_diameter_measure (R : realType) (n m : nat)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) : Prop :=
  is_caratheodory_limit
    (fun j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => exterior_diameter_cost m (val j)) mu.

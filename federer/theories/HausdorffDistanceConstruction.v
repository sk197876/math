(** Federer (1969), 2.10.21, p. 183: existence of the Hausdorff distance.
    Compactness gives maxima of each continuous distance profile on the
    other nonempty compact set; their maximum satisfies the abstract
    absolute-profile supremum laws. The witnesses in this file are private
    to the construction and sealing development. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSetDistanceProfile MetricSetDistanceUP MetricSetDistanceBasic
  MetricSetDistanceContinuity CompactMaximum HausdorffDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_profile_maximum_exists]: supporting
    attainment of each directed supremum in 2.10.21,
    p. 183, by continuous compact maximum. *)
Lemma compact_profile_maximum_exists (R : realType) (X : metricType R)
    (C D : compact_metric_set X) : exists x, val C x /\
  forall y, val C y -> compact_set_distance_profile D y<=compact_set_distance_profile D x.
Proof.
have hc := compact_set_distance_profile_specification D.
have hf : continuous (fun x : X => (compact_set_distance_profile D x : R^o)).
  exact: metric_set_distance_continuous hc.
exact: continuous_compact_maximum (set_valP C).2 (set_valP C).1 hf.
Qed.

(** Source for [hausdorff_distance_exists]: existence proof
    for the supremum specified in 2.10.21,
    p. 183. No bounded compactness of the ambient
    space is required for this part. *)
Theorem hausdorff_distance_exists (R : realType) (X : metricType R) :
  exists d : compact_metric_set X -> compact_metric_set X -> R, is_hausdorff_distance d.
Proof.
pose z C D := sval (cid (@compact_profile_maximum_exists R X C D)).
have hz C D := svalP (cid (@compact_profile_maximum_exists R X C D)).
pose d C D := Order.max (compact_set_distance_profile D (z C D))
  (compact_set_distance_profile C (z D C)).
exists d; constructor.
- move=> C D; rewrite /d le_max; apply/orP; left.
  exact: metric_set_distance_nonnegative (compact_set_distance_profile_specification D) (z C D).
- move=> C D x.
  have hCD := (proj2 (compact_distance_profile_signed_bound C D
    (compact_set_distance_profile D (z C D))) (hz C D).2) x.
  have hDC := (proj2 (compact_distance_profile_signed_bound D C
    (compact_set_distance_profile C (z D C))) (hz D C).2) x.
  rewrite ler_norml /d; apply/andP; split.
  + have hh : compact_set_distance_profile C (z D C)<=d C D by rewrite /d le_max lexx orbT.
    rewrite /d in hh; lra.
  + have hh : compact_set_distance_profile D (z C D)<=d C D by rewrite /d le_max lexx.
    exact: le_trans hCD hh.
- move=> C D b hb hbound; rewrite /d ge_max; apply/andP; split.
  + have hh := hbound (z C D).
    have he := proj2 (compact_set_distance_profile_zero C (z C D)) (hz C D).1.
    rewrite he subr0 in hh; exact: le_trans (ler_norm _) hh.
  + have hh := hbound (z D C).
    have he := proj2 (compact_set_distance_profile_zero D (z D C)) (hz D C).1.
    rewrite he sub0r normrN in hh; exact: le_trans (ler_norm _) hh.
Qed.

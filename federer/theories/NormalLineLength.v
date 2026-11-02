(** Hausdorff-length interpretation of normal sections in Federer (1969),
    2.10.30, p. 195. The isometry and its scalar orthogonal retraction
    identify ambient Hausdorff length with scalar Lebesgue length, using the
    already proved 2.10.7, pp. 174–175. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies RealMetricBackground
  UnitNormalGeometry UnitNormalMetric SteinerSymmetrisationUP CenteredSectionUP
  HausdorffLength HausdorffLengthMaps HausdorffLengthReal LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_line_hausdorff_length]: direct scalar interpretation
    of normal-line Hausdorff length in 2.10.30, p. 195 It holds for
    arbitrary subsets, with no measurability or boundedness premise. *)
Theorem normal_line_hausdorff_length (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u y : V) : B u u= 1 -> inner_coordinate hB u y=0 ->
  forall A : set (real_line_metric R),
    @hausdorff_length R (inner_metric_space hB) ((fun t=>y+t*:u) @` A)=
      lebesgue_scalar_measure A.
Proof.
move=> hu hy A.
have hf s t : mdist (y+s*:u : inner_metric_space hB) (y+t*:u : inner_metric_space hB)<=
    mdist (s : real_line_metric R) (t : real_line_metric R).
  by rewrite (@normal_line_distance R V B hB u hu y s t).
have hg := @normal_coordinate_nonexpanding R V B hB u hu.
have hk : cancel (fun t : real_line_metric R=>y+t*:u) (inner_coordinate hB u).
  by move=> t; exact (@normal_line_coordinate R V B hB u hu y t hy).
have hh := @hausdorff_length_retracted_isometry R
  [the metricType R of real_line_metric R] (inner_metric_space hB)
  (fun t=>y+t*:u) (inner_coordinate hB u) hf hg hk A.
by rewrite hausdorff_length_real_eq_lebesgue in hh.
Qed.

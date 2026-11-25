(** Federer (1969), 2.2.15, p. 71, necessity of the final target criterion:
    opaque finite Borel interpolation. The private natural-number coding is
    hidden; clients use only Borelness and finite attainment. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground FiniteBorelInterpolationUP
  FiniteBorelInterpolationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FiniteBorelInterpolationSignature.
(** Source for [value]: abstract finite interpolation pair
    supporting Federer 2.2.15, p. 71. *)
Parameter value : forall (R : realType) (Y : topologicalType) (Z : set Y),
  Y -> finite_set Z -> (real_line_metric R -> Y) * set (real_line_metric R).
(** Source for [laws]: abstract Borel and finite-attainment
    laws supporting Federer 2.2.15, p. 71. *)
Parameter laws : forall (R : realType) (Y : topologicalType) (Z : set Y)
  (y0 : Y) (hZ : finite_set Z),
  is_finite_borel_interpolation Z (@value R Y Z y0 hZ).1 (@value R Y Z y0 hZ).2.
End FiniteBorelInterpolationSignature.
Module FiniteBorelInterpolation : FiniteBorelInterpolationSignature.
(** Source for [value]: private witness selection for the
    necessity argument of Federer 2.2.15, p. 71. *)
Definition value (R : realType) (Y : topologicalType) (Z : set Y)
    (y0 : Y) (hZ : finite_set Z) :=
  let w := cid (@finite_borel_interpolation_exists R Y Z y0 hZ) in
  (projT1 w, projT1 (cid (projT2 w))).
(** Source for [laws]: the selected pair satisfies the
    interpolation laws supporting Federer 2.2.15, p. 71. *)
Lemma laws (R : realType) (Y : topologicalType) (Z : set Y)
    (y0 : Y) (hZ : finite_set Z) :
  is_finite_borel_interpolation Z (@value R Y Z y0 hZ).1 (@value R Y Z y0 hZ).2.
Proof. exact: projT2 (cid (projT2 (cid (@finite_borel_interpolation_exists R Y Z y0 hZ)))). Qed.
End FiniteBorelInterpolation.

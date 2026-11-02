(** Opaque approximate differential supporting Federer
    (1969), 3.2.16, p. 253. Public
    proofs use only the independently specified
    exact graph, not the selected representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP MeasureUP
  MeasureApproximateDifferentialUP MeasureApproximateDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MeasureApproximateDifferentialSignature.
(** Source for [value]: ap Df(a) at an actual
    approximately differentiable point, Federer 3.2.16,
    p. 253. The supplied predicate is the
    defining hypothesis, not an existence axiom. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (phi : set X -> \bar R) m, is_measure phi ->
  forall (f : partial_function X Y) a,
  measure_approximately_differentiable_at NY hNX phi m f a -> partial_function X Y.
(** Source for [laws]: the independent exact graph
    law for ap Df(a), Federer 3.2.16,
    p. 253; its domain is the approximate tangent cone. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (phi : set X -> \bar R) m (hm : is_measure phi)
  (f : partial_function X Y) a
  (ha : measure_approximately_differentiable_at NY hNX phi m f a),
  is_measure_approximate_differential NY hNX phi m f a
    (@value R X Y NX NY hNX hNY phi m hm f a ha).
End MeasureApproximateDifferentialSignature.
Module MeasureApproximateDifferential : MeasureApproximateDifferentialSignature.
(** Source for [value]: opaque selection from the
    proved graph existence for Federer 3.2.16,
    p. 253. *)
Definition value (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (phi : set X -> \bar R) m (hm : is_measure phi)
  (f : partial_function X Y) a
  (ha : measure_approximately_differentiable_at NY hNX phi m f a) :=
  projT1 (cid (@measure_approximate_differential_exists R X Y NX NY hNX hNY phi m f a hm ha)).
(** Source for [laws]: the selected graph satisfies
    the exact cone-restriction specification of Federer
    3.2.16, p. 253. *)
Lemma laws (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (phi : set X -> \bar R) m (hm : is_measure phi)
  (f : partial_function X Y) a
  (ha : measure_approximately_differentiable_at NY hNX phi m f a) :
  is_measure_approximate_differential NY hNX phi m f a
    (@value R X Y NX NY hNX hNY phi m hm f a ha).
Proof. exact: projT2 (cid (@measure_approximate_differential_exists R X Y NX NY hNX hNY phi m f a hm ha)). Qed.
End MeasureApproximateDifferential.

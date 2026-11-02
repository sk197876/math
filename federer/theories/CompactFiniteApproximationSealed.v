(** Federer (1969), 2.4.12, p. 87: sealed finite Borel approximation on
    compact sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactFiniteApproximationUP CompactFiniteApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CompactFiniteApproximationSignature.
(** Source for [value]: abstract approximating map supporting
    Federer 2.4.12, p. 87, without an exposed construction. *)
Parameter value : forall (R : realType) (Y : metricType R) (K : set Y)
  (epsilon : R) (y0 : Y), compact K -> (0 < epsilon)%R -> Y -> Y.
(** Source for [laws]: finite Borel approximation laws supporting Federer
    2.4.12, p. 87 *)
Parameter laws : forall (R : realType) (Y : metricType R) (K : set Y)
  (epsilon : R) (y0 : Y) (hK : compact K) (he : (0 < epsilon)%R),
  is_compact_finite_approximation K epsilon y0 (@value R Y K epsilon y0 hK he).
End CompactFiniteApproximationSignature.
Module CompactFiniteApproximation : CompactFiniteApproximationSignature.
(** Source for [value]: selection of the proved witness supporting
    Federer 2.4.12, p. 87. *)
Definition value (R : realType) (Y : metricType R) (K : set Y)
  (epsilon : R) (y0 : Y) (hK : compact K) (he : (0 < epsilon)%R) :=
  projT1 (cid (@compact_finite_approximation_exists R Y K epsilon y0 hK he)).
(** Source for [laws]: the witness satisfies the exposed laws,
    supporting Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (Y : metricType R) (K : set Y)
  (epsilon : R) (y0 : Y) (hK : compact K) (he : (0 < epsilon)%R) :
  is_compact_finite_approximation K epsilon y0 (@value R Y K epsilon y0 hK he).
Proof. exact: projT2 (cid (@compact_finite_approximation_exists R Y K epsilon y0 hK he)). Qed.
End CompactFiniteApproximation.

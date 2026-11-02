(** Opaque interleaved-scale witness for Federer (1969), 2.10.29, p. 194.
    Expose six sequences and their proved recurrence laws; keep recursive
    positive states and selected scalar subdivisions private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ConcaveIntervalGaugeUP InterleavedCantorScalesUP
  InterleavedCantorScalesConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type INTERLEAVED_CANTOR_SCALES.
(** Source for [value]: abstract interleaved
    scalar sequences in 2.10.29, p. 194. *)
Parameter value : forall (R : realType) (h : R -> R),
  is_concave_interval_gauge h -> interleaved_cantor_scale_data R.
(** Source for [laws]: defining root, split
    and small-spacing laws of 2.10.29,
    p. 194, from a proved witness. *)
Parameter laws : forall (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h),
  is_interleaved_cantor_scales h (@value R h hg).
End INTERLEAVED_CANTOR_SCALES.

Module InterleavedCantorScales : INTERLEAVED_CANTOR_SCALES.
(** Source for [value]: proved scalar-sequence
    witness for 2.10.29, p. 194,
    hidden by opaque module ascription. *)
Definition value (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h) :=
  projT1 (cid (@interleaved_cantor_scales_exist R h hg)).
(** Source for [laws]: recurrence specification
    for 2.10.29, p. 194, supplied
    by the encapsulated existence proof. *)
Lemma laws (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h) :
  is_interleaved_cantor_scales h (@value R h hg).
Proof. exact: (projT2 (cid (@interleaved_cantor_scales_exist R h hg))). Qed.
End InterleavedCantorScales.

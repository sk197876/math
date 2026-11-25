(** Federer (1969), 4.1.15, p. 373: an opaque actual
    sequence for the finite-mass nonconvergence example.
    Consumers receive only the independent family laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations PointOneOscillatingMapsUP
  PointOneOscillatingMapsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type PointOneOscillatingMapsSignature.
(** Source for [value]: a smooth compact sequence of
    the kind used in 4.1.15, p. 373. *)
Parameter value:forall R:realType,nat->R_n R 1%N->R_n R 1%N.
(** Source for [laws]: precisely the independently stated
    quantitative example laws for 4.1.15, p. 373. *)
Parameter laws:forall R:realType,@is_point_one_oscillating_maps R (@value R).
End PointOneOscillatingMapsSignature.

Module PointOneOscillatingMaps:PointOneOscillatingMapsSignature.
(** Source for [value]: hide the separately proved
    example witness of 4.1.15, p. 373. *)
Definition value (R:realType):nat->R_n R 1%N->R_n R 1%N:=
  projT1 (cid (@point_one_oscillating_maps_exists R)).
(** Source for [laws]: the chosen witness satisfies the
    independent example laws, 4.1.15, p. 373. *)
Lemma laws (R:realType):@is_point_one_oscillating_maps R (@value R).
Proof.
exact:(projT2 (cid (@point_one_oscillating_maps_exists R))).
Qed.
End PointOneOscillatingMaps.
Arguments PointOneOscillatingMaps.value : clear implicits.
Arguments PointOneOscillatingMaps.laws : clear implicits.

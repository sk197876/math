(** Federer (1969), 4.1.12, p. 369: seal
    the proved unit-scale smooth cutoff. Consumers
    use only its independently specified support,
    range, unit value and Lipschitz laws. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentUnitIntervalCutoffUP CurrentUnitIntervalCutoffExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CurrentUnitIntervalCutoffSignature.
(** Source for [value]: a unit-scale smooth
    cutoff for the original phi_k in
    Federer 4.1.12, p. 369. *)
Parameter value:forall R:realType,R_n R 1%N->R^o.
(** Source for [laws]: the independent smoothness,
    support, range and sharp Lipschitz specification
    for the original cutoffs of Federer
    4.1.12, p. 369. *)
Parameter laws:forall R:realType,is_current_unit_interval_cutoff (@value R).
End CurrentUnitIntervalCutoffSignature.

Module CurrentUnitIntervalCutoff:CurrentUnitIntervalCutoffSignature.
(** Source for [value]: select the proved
    cutoff witness behind the opaque interface,
    supporting Federer 4.1.12, p. 369. *)
Definition value (R:realType):R_n R 1%N->R^o:=
  projT1 (cid (@current_unit_interval_cutoff_exists R)).
(** Source for [laws]: the hidden witness
    satisfies every independent cutoff law,
    supporting Federer 4.1.12, p. 369. *)
Lemma laws (R:realType):is_current_unit_interval_cutoff (@value R).
Proof. exact:projT2 (cid (@current_unit_interval_cutoff_exists R)). Qed.
End CurrentUnitIntervalCutoff.

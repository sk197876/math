(** Federer (1969), 3.4.10, p. 337:
    opaque original regular part after proved unique
    existence. Only the neighbourhood laws are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations AnalyticRegularLocusUP AnalyticRegularLocusExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticRegularLocusSignature.
(** Source for [value]: the regular part R
    of 3.4.10, p. 337, at the
    original global dimension. *)
Parameter value:forall (R:realType) (n m:nat),set (R_n R n)->set (R_n R n)->set (R_n R n).
(** Source for [laws]: the exact original neighbourhood
    criterion of 3.4.10, p. 337. *)
Parameter laws:forall (R:realType) n m (U S:set (R_n R n)),
  is_analytic_regular_locus m U S (@value R n m U S).
End AnalyticRegularLocusSignature.
Module AnalyticRegularLocus:AnalyticRegularLocusSignature.
(** Source for [value]: private set selection after
    proved existence, 3.4.10, p. 337. *)
Definition value (R:realType) n m (U S:set (R_n R n)):=
  projT1 (cid (@analytic_regular_locus_exists R n m U S)).
(** Source for [laws]: the selected regular part
    satisfies the independent original condition,
    3.4.10, p. 337. *)
Lemma laws (R:realType) n m (U S:set (R_n R n)):
  is_analytic_regular_locus m U S (@value R n m U S).
Proof. exact:(projT2 (cid (@analytic_regular_locus_exists R n m U S))). Qed.
End AnalyticRegularLocus.

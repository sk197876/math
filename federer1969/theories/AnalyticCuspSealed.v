(** Federer (1969), 3.4.11, p. 338:
    the original plane cusp is opaque after
    proved unique existence; only equation laws are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations AnalyticCuspUP AnalyticCuspExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticCuspSignature.
(** Source for [set]: the original plane cusp,
    3.4.11, p. 338. *)
Parameter set:forall R:realType,set (R_n R 2).
(** Source for [laws]: the exact original polynomial
    equation, 3.4.11, p. 338. *)
Parameter laws:forall R:realType,is_analytic_cusp (@set R).
End AnalyticCuspSignature.
Module AnalyticCusp:AnalyticCuspSignature.
(** Source for [set]: private choice after proved
    existence of the original cusp, 3.4.11, p. 338. *)
Definition set (R:realType):set (R_n R 2):=projT1 (cid (@analytic_cusp_exists R)).
(** Source for [laws]: the chosen witness satisfies
    the independent original equation, 3.4.11, p. 338. *)
Lemma laws (R:realType):is_analytic_cusp (@set R).
Proof. exact:(projT2 (cid (@analytic_cusp_exists R))). Qed.
End AnalyticCusp.

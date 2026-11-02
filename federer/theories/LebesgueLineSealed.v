(** Opaque selection of the uniquely characterised scalar
    Lebesgue measure for Federer (1969), 2.6.5, pp. 119–120.
    The Riemann-integral witness remains private. Sources and
    editions: LebesgueLineUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueLineUP LebesgueLineConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type LebesgueLineSignature.
(** Source for [value]: the scalar measure L^1 from
    Federer 2.5.17, p. 111, used in 2.6.5, p. 119. *)
Parameter value : forall R : realType, set R -> \bar R.
(** Source for [laws]: the defining laws of L^1 in
    Federer 2.5.17, p. 111; the witness must prove them. *)
Parameter laws : forall R : realType, is_lebesgue_line_measure (@value R).
End LebesgueLineSignature.
Module LebesgueLine : LebesgueLineSignature.
(** Source for [value]: private choice from proved existence
    in Federer 2.5.17, p. 111, for 2.6.5. *)
Definition value R := projT1 (cid (@lebesgue_line_laws_exist R)).
(** Source for [laws]: the chosen witness satisfies the
    laws in Federer 2.5.17, p. 111. *)
Lemma laws R : is_lebesgue_line_measure (@value R).
Proof. exact: projT2 (cid (@lebesgue_line_laws_exist R)). Qed.
End LebesgueLine.

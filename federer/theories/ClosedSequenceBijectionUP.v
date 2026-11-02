(** Federer (1969), 2.2.10, p. 66: a closed subset B of the sequence space
    admits a univalent continuous map onto R. The interface below exposes a
    continuous extension to all of N; the restriction to B is the printed
    bijection. This extension is a proved strengthening, obtained by using
    constant maps on the other cylinders, not an additional premise in the
    final existence theorem. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_closed_sequence_bijection]: abstract closed- domain
    representation supporting Federer 2.2.10, p. 66. B is closed, psi is
    continuous, and its restriction to B is one-to-one and onto the target.
    Global continuity of the extension is stronger than the printed
    continuity on B and is proved by cylinder pasting. *)
Record is_closed_sequence_bijection (R : realType) (T : topologicalType)
    (B : set (positive_sequence_space R)) (psi : positive_sequence_space R -> T) : Prop := {
  closed_sequence_bijection_domain_closed : closed B;
  closed_sequence_bijection_continuous : continuous psi;
  closed_sequence_bijection_injective : forall m n, B m -> B n -> psi m = psi n -> m = n;
  closed_sequence_bijection_surjective : psi @` B = setT
}.

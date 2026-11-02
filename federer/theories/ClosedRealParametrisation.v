(** Federer (1969), 2.2.10, p. 66: public closed-domain continuous bijection
    from the sequence space onto R. Only the sealed specification is used.
    Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace RealMetricBackground
  ClosedSequenceBijectionUP ClosedRealParametrisationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [closed_real_sequence_parametrisation]: direct existence
    assertion used by Federer 2.2.10, p. 66: a closed subset B of N admits a
    continuous bijection onto R. The exposed extension is continuous on all
    N, a proved strengthening; its restriction to B is the printed map. No
    private witness is unfolded here. *)
Theorem closed_real_sequence_parametrisation (R : realType) :
  exists (B : set (positive_sequence_space R))
    (psi : positive_sequence_space R -> real_line_metric R),
    is_closed_sequence_bijection B psi.
Proof.
exists (@ClosedRealParametrisation.value R).1, (@ClosedRealParametrisation.value R).2.
exact: ClosedRealParametrisation.laws.
Qed.

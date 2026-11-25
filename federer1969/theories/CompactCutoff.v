(** Public cutoff interface for Federer (1969), 2.5.13, p. 106. Exact laws
    and Source context: CompactCutoffUP.v. All subsequent use is through the
    opaque specification. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import CompactCutoffUP CompactCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [compact_cutoff]: public cutoff equal to one
    on K, used in Federer 2.5.13, p. 106, and
    2.5.14, p. 107. *)
Definition compact_cutoff (R : realType) (X : topologicalType) (K : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) :=
  @CompactCutoff.value R X K hh hl hK.

(** Source for [compact_cutoff_specification]: the exposed
    support, range and equality laws of the cutoff supporting
    Federer 2.5.13, pp. 106–107. *)
Lemma compact_cutoff_specification (R : realType) (X : topologicalType) (K : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) :
  is_compact_cutoff K (@compact_cutoff R X K hh hl hK).
Proof. exact: CompactCutoff.laws. Qed.

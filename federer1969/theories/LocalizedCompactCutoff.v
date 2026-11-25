(** Public cutoff interface for Federer (1969), 2.5.14, pp. 107–108. Exact
    laws and Source context: LocalizedCompactCutoffUP.v. All subsequent use
    is through the opaque specification. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import LocalizedCompactCutoffUP LocalizedCompactCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [localized_compact_cutoff]: public cutoff equal to one
    on K with support in V, supporting Federer 2.5.14,
    pp. 107–108. *)
Definition localized_compact_cutoff (R : realType) (X : topologicalType) (K V : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) (hV : open V) (hKV : K `<=` V) :=
  @LocalizedCompactCutoff.value R X K V hh hl hK hV hKV.

(** Source for [localized_compact_cutoff_specification]: the exposed
    support, range and equality laws of the cutoff supporting
    Federer 2.5.14, pp. 107–108. *)
Lemma localized_compact_cutoff_specification (R : realType) (X : topologicalType) (K V : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) (hV : open V) (hKV : K `<=` V) :
  is_localized_compact_cutoff K V (@localized_compact_cutoff R X K V hh hl hK hV hKV).
Proof. exact: LocalizedCompactCutoff.laws. Qed.

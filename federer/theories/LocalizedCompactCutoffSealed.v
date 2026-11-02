(** Opaque cutoff witness for Federer (1969), 2.5.14, pp. 107–108. Exact
    laws and Source context: LocalizedCompactCutoffUP.v. The
    general-topology construction is private. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import LocalizedCompactCutoffUP LocalizedCompactCutoffConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type LocalizedCompactCutoffSignature.
(** Source for [value]: abstract cutoff used in Federer
    2.5.14, pp. 107–108. *)
Parameter value : forall (R : realType) (X : topologicalType) (K V : set X),
  hausdorff_space X -> locally_compact (@setT X) -> compact K -> open V -> K `<=` V -> X -> R.
(** Source for [laws]: the compact-support, range and equality
    laws used in Federer 2.5.14, pp. 107–108. *)
Parameter laws : forall (R : realType) (X : topologicalType) (K V : set X)
  (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) (hV : open V) (hKV : K `<=` V),
  is_localized_compact_cutoff K V (@value R X K V hh hl hK hV hKV).
End LocalizedCompactCutoffSignature.
Module LocalizedCompactCutoff : LocalizedCompactCutoffSignature.
(** Source for [value]: private witness choice for the cutoff
    in Federer 2.5.14, pp. 107–108. *)
Definition value (R : realType) (X : topologicalType) (K V : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) (hV : open V) (hKV : K `<=` V) :=
  projT1 (cid (@localized_compact_cutoff_exists R X K V hh hl hK hV hKV)).
(** Source for [laws]: the proved witness satisfies the cutoff
    specification supporting Federer 2.5.14, pp. 107–108. *)
Lemma laws (R : realType) (X : topologicalType) (K V : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) (hV : open V) (hKV : K `<=` V) :
  is_localized_compact_cutoff K V (@value R X K V hh hl hK hV hKV).
Proof. exact: projT2 (cid (@localized_compact_cutoff_exists R X K V hh hl hK hV hKV)). Qed.
End LocalizedCompactCutoff.

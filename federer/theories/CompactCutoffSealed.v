(** Opaque cutoff witness for Federer (1969), 2.5.13, p. 106. Exact laws and
    Source context: CompactCutoffUP.v. The general-topology construction is
    private. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import CompactCutoffUP CompactCutoffConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CompactCutoffSignature.
(** Source for [value]: abstract cutoff used in Federer
    2.5.13, p. 106. *)
Parameter value : forall (R : realType) (X : topologicalType) (K : set X),
  hausdorff_space X -> locally_compact (@setT X) -> compact K -> X -> R.
(** Source for [laws]: the compact-support, range and equality
    laws used in Federer 2.5.13, pp. 106–107. *)
Parameter laws : forall (R : realType) (X : topologicalType) (K : set X)
  (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K),
  is_compact_cutoff K (@value R X K hh hl hK).
End CompactCutoffSignature.
Module CompactCutoff : CompactCutoffSignature.
(** Source for [value]: private witness choice for the cutoff
    in Federer 2.5.13, p. 106. *)
Definition value (R : realType) (X : topologicalType) (K : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) :=
  projT1 (cid (@compact_cutoff_exists R X K hh hl hK)).
(** Source for [laws]: the proved witness satisfies the cutoff
    specification supporting Federer 2.5.13, p. 106. *)
Lemma laws (R : realType) (X : topologicalType) (K : set X)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K) :
  is_compact_cutoff K (@value R X K hh hl hK).
Proof. exact: projT2 (cid (@compact_cutoff_exists R X K hh hl hK)). Qed.
End CompactCutoff.

(** Federer (1969), 2.2.9, p. 65: existence of the map g by selecting the
    unique branch points. The selection is private and will be sealed; all
    consequences use is_open_embedding_map. Source context and encoding:
    OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP OpenEmbeddingTreeUP
  SequenceTreePrefixes OpenEmbeddingBranches OpenEmbeddingMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [open_embedding_map_exists]: Federer 2.2.9,
    p. 65, existence of g(n) for every coordinate sequence.
    Its defining branch membership laws follow from the previously
    proved closed shrinking intersection theorem. *)
Theorem open_embedding_map_exists (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_open_embedding_tree E) :
  exists g : positive_sequence_space R -> T, is_open_embedding_map E g.
Proof.
exists (fun n => projT1 (cid (open_embedding_branch_point_exists hT hE n)))=> n k.
exact: (projT2 (cid (open_embedding_branch_point_exists hT hE n)) k).
Qed.

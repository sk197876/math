(** Federer (1969), 2.2.10, p. 65: the image of a continuous map from N into
    a Hausdorff space is Suslin. The closed witness is the displayed graph
    in X times N. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP ContinuousClosedGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_sequence_image_suslin]: direct image
    assertion in Federer 2.2.10, p. 65, with its printed
    Hausdorff target hypothesis. The graph's projection is exactly
    the image of f; the graph is closed by continuity and separation. *)
Theorem continuous_sequence_image_suslin (R : realType) (T : topologicalType)
    (f : positive_sequence_space R -> T) :
  hausdorff_space T -> continuous f -> is_suslin_set R (f @` setT).
Proof.
move=> hT hf; exists [set p : T * positive_sequence_space R | p.1 = f p.2]; split.
- exact: continuous_map_closed_graph hT hf.
- apply/seteqP; split.
  + move=> x [[y n] hn <-]; exists n=> //; exact: esym hn.
  + move=> x [n _ <-]; by exists (f n,n).
Qed.

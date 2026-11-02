(** Federer (1969), 2.2.9, p. 65: the displayed set Gamma is the
    intersection, over positive levels, of the unions of the open sets U(s)
    on that level. Hence it is a Borel set. Source context and word
    encoding: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import TopologicalBorel OpenEmbeddingTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_level]: supporting level union
    in the displayed formula for Gamma, Federer 2.2.9, p. 65. *)
Definition open_embedding_level (T : topologicalType) (U : seq nat -> set T) k :=
  \bigcup_(s in [set s | size s = k]) U s.

(** Source for [open_embedding_image]: Federer 2.2.9,
    p. 65, the displayed intersection of the positive-level open
    unions. This is defined independently of any chosen branch map. *)
Definition open_embedding_image (T : topologicalType) (U : seq nat -> set T) : set T :=
  \bigcap_(k : nat) open_embedding_level U k.+1.

(** Source for [open_embedding_level_open]: supporting openness
    for Federer 2.2.9, p. 65: each level is a union of
    open sets, without any separability requirement on the target. *)
Lemma open_embedding_level_open (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) k :
  open (open_embedding_level U k).
Proof.
apply: bigcup_open=> s _; exact: (@open_embedding_tree_open R T U hU s).
Qed.

(** Source for [open_embedding_image_borel]: direct Borel assertion for the
    displayed Gamma in Federer 2.2.9, p. 65, as a countable intersection of
    open sets. *)
Lemma open_embedding_image_borel (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) :
  borel_set (open_embedding_image U).
Proof.
apply: borel_set_countable_intersection; first exact: countableP.
- by exists 0%N.
- move=> k _; apply: open_borel_set; exact: (@open_embedding_level_open R T U hU k.+1).
Qed.

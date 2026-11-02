(** Federer (1969), 2.2.9, p. 65, the real-line refinement: intervals may be
    chosen so that the complement of Gamma is countable. This module
    isolates the countable-loss argument from the interval construction.
    Source context and reversed word convention: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import OpenEmbeddingTreeUP OpenEmbeddingBorelImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_child_loss]: supporting definition
    for Federer 2.2.9, p. 65: the points of one open branch
    set that belong to none of its immediate children. *)
Definition open_embedding_child_loss (T : topologicalType)
    (U : seq nat -> set T) s : set T :=
  U s `\` (\bigcup_(j : nat) U (j::s)).

(** Source for [open_embedding_complement_loss_cover]: supporting
    argument for Federer 2.2.9, p. 65: every point outside
    Gamma is lost at a finite stage, hence lies in one child-loss
    set. This does not require completeness or a chosen branch map. *)
Lemma open_embedding_complement_loss_cover (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) :
  ~` open_embedding_image U `<=`
    \bigcup_(s : seq nat) open_embedding_child_loss U s.
Proof.
move=> x hx; apply: contrapT=> hn; apply: hx.
have hlevel k : exists s, size s = k /\ U s x.
  elim: k=> [|k [s [hs hxs]]].
  - exists [::]; split=> //; by rewrite (open_embedding_tree_root hU).
  - have hc : exists j, U (j::s) x.
      apply: contrapT=> hnone; apply: hn; exists s=> //; split=> //.
      by move=> [j _ hj]; apply: hnone; exists j.
    have [j hj] := hc; exists (j::s); split=> //; by rewrite /= hs.
move=> k _; have [s [hs hxs]] := hlevel k.+1; by exists s.
Qed.

(** Source for [open_embedding_image_countable_complement]: supporting
    countability step in Federer 2.2.9, p. 65. The interval construction
    must separately establish the child-loss premise. *)
Theorem open_embedding_image_countable_complement (R : realType)
    (T : metricType R) (U : seq nat -> set T) (hU : is_open_embedding_tree U) :
  (forall s, countable (open_embedding_child_loss U s)) ->
  countable (~` open_embedding_image U).
Proof.
move=> hc; apply: sub_countable (subset_card_le
  (@open_embedding_complement_loss_cover R T U hU)) _.
apply: bigcup_countable; first exact: countableP.
by move=> s _; exact: hc.
Qed.

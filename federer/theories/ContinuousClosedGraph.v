(** Federer (1969), 2.2.10, p. 65: a continuous map from the sequence space
    into a Hausdorff space has closed graph, so its image is a closed
    projection. The supporting closed-graph lemma below allows any
    topological domain. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_map_closed_graph]: supporting closed-
    graph assertion in Federer 2.2.10, p. 65: the graph
    {(y,x): y=f(x)} is closed for a continuous f into a
    Hausdorff space. Disjoint neighborhoods of y and f(x) give
    an open product neighborhood outside the graph. *)
Lemma continuous_map_closed_graph (X Y : topologicalType) (f : X -> Y) :
  hausdorff_space Y -> continuous f -> closed [set p : Y * X | p.1 = f p.2].
Proof.
move=> hY hf; rewrite -openC openE=> -[y x] hneq.
have hne : y != f x by apply/negP=> /eqP heq; exact: hneq heq.
rewrite open_hausdorff in hY.
have [[A B] [hy hx] [ha hb /eqP hdis]] := hY y (f x) hne.
have hyA : A y by move: hy; rewrite inE.
have hfxB : B (f x) by move: hx; rewrite inE.
rewrite openE in ha hb.
have hnA : nbhs y A := ha y hyA.
have hnB : nbhs x (f @^-1` B) := hf x B (hb (f x) hfxB).
exists (A, f @^-1` B); first by split.
move=> [y' x'] /= [hy' hx'] heq.
have hh : (A `&` B) y' by split=> //; rewrite heq; exact hx'.
by rewrite hdis in hh.
Qed.

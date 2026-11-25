(** General-topology support for Federer (1969), 2.6.6, pp. 120–121: the
    compatibility equations for an inverse limit define closed sets in the
    full product. The proof uses disjoint neighborhoods in a Hausdorff
    target. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_equalizer_closed]: supporting closedness
    of inverse-limit compatibility constraints, Federer 2.6.6,
    pp. 120–121. This is general topology, not a separately
    numbered claim in Federer. *)
Lemma continuous_equalizer_closed (X Y : topologicalType) (f g : X -> Y) :
  hausdorff_space Y -> continuous f -> continuous g -> closed [set x | f x=g x].
Proof.
move=> hY hf hg; rewrite -openC openE=> x hneq.
have hne : f x != g x by apply/negP=> /eqP he; exact: hneq he.
rewrite open_hausdorff in hY.
have [[U V] [hu hv] [hU hV /eqP hUV]] := hY (f x) (g x) hne.
have hfx : U (f x) by move: hu; rewrite inE.
have hgx : V (g x) by move: hv; rewrite inE.
rewrite openE in hU hV.
have hnU : nbhs x (f @^-1` U) := hf x U (hU _ hfx).
have hnV : nbhs x (g @^-1` V) := hg x V (hV _ hgx).
apply: filterS (filterI hnU hnV)=> y [hyU hyV] he.
have hh : (U `&` V) (f y) by split=> //; rewrite he.
by rewrite hUV in hh.
Qed.

(** Federer (1969), 2.2.15, p. 71, final target criterion: a function of a
    Borel countable label is Borel. Open preimages are unions of its Borel
    fibres. This uses only the project's Borel closure laws. *)
From mathcomp Require Import all_boot classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelFunctionUP BorelDiscreteIndexUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_function_of_discrete_index]: supporting
    countable step-function fact for Federer 2.2.15, p. 71.
    No continuity or measurability assumption is required on
    the assigned sequence of target values. *)
Theorem borel_function_of_discrete_index (X Y : topologicalType)
    (q : X -> nat) (y : nat -> Y) :
  has_borel_index_fibres q -> is_borel_function (y \o q).
Proof.
move=> hq U hU.
have he : (y \o q) @^-1` U = \bigcup_(n in [set n | U (y n)]) [set x | q x = n].
  apply/seteqP; split.
  - move=> x hx; by exists (q x).
  - by move=> x [n hn he]; change (U (y (q x))); rewrite he.
rewrite he; apply: borel_set_countable_union; first exact: countableP.
by move=> n hn; exact: hq n.
Qed.

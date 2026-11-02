(** Federer (1969), 2.10.40, printed p. 200: compactness bounds the positive
    radii away from zero and bounds them above. This supporting general
    extreme-value lemma gives the bounds for any positive continuous scalar
    function on a nonempty compact set. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_positive_scalar_bounds]: supporting
    positive lower and finite upper bounds for the
    radii in 2.10.40, p. 200. Both bounds
    are attained values of the given scalar function. *)
Theorem compact_positive_scalar_bounds (R : realType) (X : topologicalType)
    (P : set X) (f : X -> R^o) :
  P !=set0 -> compact P -> continuous f -> (forall x, P x -> 0<f x) ->
  exists a b, P a /\ P b /\ 0<f a /\
    forall x, P x -> f a<=f x<=f b.
Proof.
move=> hne hc hf hpos.
have hn : continuous (fun x : X=>(-f x : R^o)).
  move=> x; exact: continuousN (hf x).
have [a [ha hmin]] := @continuous_compact_maximum R X P (fun x=>(-f x : R^o)) hne hc hn.
have [b [hb hmax]] := @continuous_compact_maximum R X P f hne hc hf.
exists a,b; split=> //; split=> //; split; first exact: hpos.
move=> x hx; apply/andP; split; last exact: hmax x hx.
by have hh := hmin x hx; rewrite lerN2 in hh.
Qed.

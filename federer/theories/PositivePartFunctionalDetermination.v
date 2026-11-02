(** Federer (1969), 2.5.7, p. 99: extend equality of linear functionals from
    L+ to L by positive and negative parts. This supporting abstract lemma
    requires only additivity on a vector function lattice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws LatticeAdditiveFunctional VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_lattice_additive_positive_determination]:
    positive-part extension in Federer 2.5.7, p. 99 The scalar identity is
    proved pointwise, and both parts are proved members of the lattice. *)
Theorem vector_lattice_additive_positive_determination (R : realType) (X : Type)
    (L : set (X -> R)) (A B : (X -> R) -> R) :
  is_vector_function_lattice L -> is_lattice_additive_functional L A -> is_lattice_additive_functional L B ->
  (forall f, positive_function_lattice L f -> A f=B f) -> forall f, L f -> A f=B f.
Proof.
move=> hL hA hB he f hf.
pose u x := Order.max (f x) 0.
pose v x := Order.max (-f x) 0.
have hu : positive_function_lattice L u.
  split; first exact: (@function_lattice_positive_part R X L hL.1 f hf).
  by move=> x; rewrite /u le_max lexx orbT.
have hv : positive_function_lattice L v.
  split; first exact: (@function_lattice_negative_part R X L hL.1 f hf).
  by move=> x; rewrite /v le_max lexx orbT.
have hdecomp : (fun x => u x-v x)=f.
  apply: funext=> x; rewrite /u /v; case: (leP 0 (f x))=> hx.
  - by rewrite max_r ?oppr_le0 // subr0.
  - by rewrite max_l ?oppr_ge0 ?ltW // sub0r opprK.
rewrite -hdecomp (@vector_lattice_additive_difference R X L A hL hA u v hu.1 hv.1)
  (@vector_lattice_additive_difference R X L B hL hB u v hu.1 hv.1).
by rewrite (he u hu) (he v hv).
Qed.

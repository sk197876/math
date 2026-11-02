(** Federer (1969), 2.5.8, p. 100: a Daniell integral on the total
    L-infinity vector lattice is linear. This supporting consequence of
    additivity and positive homogeneity uses 2.5.5, p. 96. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP VectorFunctionLattice
  FunctionLatticeSeminormUP DaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_daniell_integral_linear]: supporting passage from
    Daniell to linear hypotheses in Federer 2.5.8, p. 100 Negative
    homogeneity follows from additivity on the vector lattice, not an extra
    axiom. *)
Lemma vector_daniell_integral_linear (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_vector_function_lattice L -> is_daniell_integral L A ->
  is_linear_functional_on_functions L A.
Proof.
move=> hL hA; split; first exact: (@daniell_integral_add R X L A hA).
move=> c f hf; case: (leP 0 c)=> hc.
- exact: (@daniell_integral_scale R X L A hA c f hc hf).
- have hn : (0 <= -c)%R by rewrite oppr_ge0; exact: ltW hc.
  have hs := @daniell_integral_scale R X L A hA (-c) f hn hf.
  have hneg := @vector_lattice_additive_negation R X L A hL
    (@daniell_integral_add R X L A hA) (fun x => (-c)*f x) (hL.2.2 _ _ hf).
  have he : (fun x => -((-c)*f x))=(fun x => c*f x).
    by apply: funext=> x; rewrite mulNr opprK.
  by rewrite he hs mulNr opprK in hneg.
Qed.

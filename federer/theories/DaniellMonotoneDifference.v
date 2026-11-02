(** Federer (1969), 2.5.7, p. 99: the residual nu is a Daniell integral on
    L+. This supporting theorem proves that the difference of two monotone
    Daniell integrals is a Daniell integral on their common lattice. The
    ordinary convergence requirement is essential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellIntegralUP RealDifferenceOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [difference_of_monotone_daniell_integrals]: supporting
    justification of the residual functional in Federer 2.5.7, p. 99 Empty
    lattices are allowed, with all four laws then vacuous. *)
Theorem difference_of_monotone_daniell_integrals (R : realType) (X : Type)
    (L : set (X -> R)) (A B : (X -> R) -> R) :
  is_function_lattice L -> is_monotone_daniell_integral L A -> is_monotone_daniell_integral L B ->
  is_daniell_integral L (fun f => (A f-B f)%R).
Proof.
move=> hL hA hB; constructor.
- move=> f g hf hg.
  rewrite (monotone_daniell_integral_add hA hf hg) (monotone_daniell_integral_add hB hf hg).
  by rewrite opprD addrACA.
- move=> c f hc hf.
  by rewrite (monotone_daniell_integral_scale hA hc hf) (monotone_daniell_integral_scale hB hc hf) mulrBr.
- move=> f hf; exists (A f-B (fun _ => 0%R))%R=> k [hk [hk0 hkf]].
  have hz := @function_lattice_zero R X L hL f hf.
  have ha := @monotone_daniell_integral_monotone R X L A hA k f hk hf hkf.
  have hb := @monotone_daniell_integral_monotone R X L B hB (fun _ => 0%R) k hz hk hk0.
  exact: lerB ha hb.
- move=> f g hf hg hfg.
  exact: (@real_difference_order_limit R (fun n => A (f n)) (fun n => B (f n)) (A g) (B g)
    (@monotone_daniell_integral_increases R X L A hA f g hf hg hfg).2
    (@monotone_daniell_integral_increases R X L B hB f g hf hg hfg).2).
Qed.

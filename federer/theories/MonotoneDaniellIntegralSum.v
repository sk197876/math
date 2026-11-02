(** Federer (1969), 2.5.6, p. 97: a monotone Daniell integral is a Daniell
    integral, and 2.5.11, p. 102: the functional lambda is the sum of two
    integral functionals on a common lattice. These supporting closure laws
    of the specifications in 2.5.2, p. 92, and 2.5.5, p. 96, use only the
    four functional laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP DaniellIntegralUP
  ExtendedRealOrderLimit RealSequenceLimitArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_increases_to_add]: supporting addition of
    increasing real sequences for the sum functional in Federer
    2.5.11, p. 102, by the limit arithmetic of 2.1.1, p. 51. *)
Lemma extended_increases_to_add (R : realType) (u v : nat -> R) (a b : R) :
  extended_increases_to (fun n => (u n)%:E) a%:E ->
  extended_increases_to (fun n => (v n)%:E) b%:E ->
  extended_increases_to (fun n => (u n+v n)%R%:E) (a+b)%R%:E.
Proof.
move=> [hu hu'] [hv hv']; split; last exact: real_sequence_limit_add hu' hv'.
move=> n m hnm; have := hu n m hnm; have := hv n m hnm; rewrite !lee_fin.
by move=> h1 h2; exact: lerD.
Qed.

(** Source for [monotone_daniell_integral_sum]: the functional
    lambda(f)=integral f d(alpha_1 x beta_2)+integral f d(beta_1 x alpha_2)
    in Federer 2.5.11, p. 102, is a monotone Daniell integral because
    each summand satisfies the four laws of 2.5.2, p. 92. *)
Theorem monotone_daniell_integral_sum (R : realType) (X : Type)
    (L : set (X -> R)) (A B : (X -> R) -> R) :
  is_monotone_daniell_integral L A -> is_monotone_daniell_integral L B ->
  is_monotone_daniell_integral L (fun f => (A f+B f)%R).
Proof.
move=> hA hB; constructor.
- move=> f g hf hg.
  by rewrite (monotone_daniell_integral_add hA hf hg) (monotone_daniell_integral_add hB hf hg) addrACA.
- move=> c f hc hf.
  by rewrite (monotone_daniell_integral_scale hA hc hf) (monotone_daniell_integral_scale hB hc hf) mulrDr.
- move=> f g hf hg hfg.
  exact: lerD (monotone_daniell_integral_monotone hA hf hg hfg)
    (monotone_daniell_integral_monotone hB hf hg hfg).
- move=> f g hf hg hfg.
  exact: extended_increases_to_add (monotone_daniell_integral_increases hA hf hg hfg)
    (monotone_daniell_integral_increases hB hf hg hfg).
Qed.

(** Source for [monotone_daniell_integral_is_daniell]: Federer
    2.5.6, p. 97, first sentence: a monotone Daniell integral in the
    sense of 2.5.2 is a Daniell integral in the sense of 2.5.5.
    Monotonicity bounds each positive order interval by the value
    at its top, and increasing convergence gives ordinary convergence. *)
Theorem monotone_daniell_integral_is_daniell (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_monotone_daniell_integral L A -> is_daniell_integral L A.
Proof.
move=> hA; constructor.
- exact: monotone_daniell_integral_add hA.
- exact: monotone_daniell_integral_scale hA.
- move=> f hf; exists (A f)=> k [hk [_ hkf]].
  have h := @monotone_daniell_integral_monotone R X L A hA k f hk hf hkf.
  exact: h.
- move=> f g hf hg hfg.
  exact: (monotone_daniell_integral_increases hA hf hg hfg).2.
Qed.

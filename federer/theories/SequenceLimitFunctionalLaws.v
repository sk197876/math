(** Federer (1969), 2.5.3, p. 95: the sequence limit functional satisfies
    the first three hypotheses of 2.5.2. We prove arbitrary real homogeneity
    and order preservation, so in particular the three printed Federer
    properties hold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ConvergentSequenceLattice SequenceLimitFunctionalUP
  RealSequenceLimitArithmetic RealScalarOrderLimits ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_limit_functional_add]: first hypothesis for the
    example in Federer 2.5.3, p. 95 *)
Lemma sequence_limit_functional_add (R : realType) (A : (nat -> R) -> R)
    (hA : is_sequence_limit_functional A) (f g : nat -> R) :
  convergent_real_sequences f -> convergent_real_sequences g ->
  A (fun n => (f n+g n)%R)=(A f+A g)%R.
Proof.
move=> hf hg; apply: (@sequence_limit_functional_value R A hA _ (A f+A g)%R).
exact: (real_sequence_limit_add (hA f hf) (hA g hg)).
Qed.

(** Source for [sequence_limit_functional_scale]: homogeneity for the
    example in Federer 2.5.3, p. 95 Arbitrary real scalars strengthen the
    nonnegative-scalar hypothesis being tested. *)
Lemma sequence_limit_functional_scale (R : realType) (A : (nat -> R) -> R)
    (hA : is_sequence_limit_functional A) (f : nat -> R) (c : R) :
  convergent_real_sequences f -> A (fun n => (c*f n)%R)=(c*A f)%R.
Proof.
move=> hf; apply: (@sequence_limit_functional_value R A hA _ (c*A f)%R).
exact: (@real_scalar_order_limit R f (A f) c (hA f hf)).
Qed.

(** Source for [sequence_limit_functional_monotone]: third hypothesis for
    the example in Federer 2.5.3, p. 95 The difference of ordered sequences
    has a nonnegative limit. *)
Lemma sequence_limit_functional_monotone (R : realType) (A : (nat -> R) -> R)
    (hA : is_sequence_limit_functional A) (f g : nat -> R) :
  convergent_real_sequences f -> convergent_real_sequences g -> function_le f g -> (A f <= A g)%R.
Proof.
move=> hf hg hfg.
have hlim := real_sequence_limit_subtract (hA g hg) (hA f hf).
have hnon : (0 : \bar R) <= (A g-A f)%R%:E.
  apply: (extended_order_limit_lower_bound hlim)=> n.
  by rewrite lee_fin subr_ge0; exact: hfg.
by move: hnon; rewrite lee_fin subr_ge0.
Qed.

(** Source for [sequence_limit_functional_constant]: constant sequences in
    the counterexample of Federer 2.5.3, p. 95 *)
Lemma sequence_limit_functional_constant (R : realType) (A : (nat -> R) -> R)
    (hA : is_sequence_limit_functional A) (c : R) : A (fun _ => c)=c.
Proof.
exact: (@sequence_limit_functional_value R A hA (fun _ => c) c (real_constant_order_limit c)).
Qed.

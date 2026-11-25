(** Federer (1969), 2.5.3, p. 95, final paragraph: L is the set of all
    convergent real sequences. We index the positive integers by n+1 for n
    in nat; this reindexing leaves both sequence convergence and pointwise
    order unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ExtendedRealOrderLimit RealScalarOrderLimits RealSequenceLimitArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergent_real_sequences]: direct lattice L in Federer
    2.5.3, p. 95, final paragraph The limit is finite real. *)
Definition convergent_real_sequences (R : realType) : set (nat -> R) :=
  [set f | exists a : R, extended_order_limit (fun n => (f n)%:E) a%:E].

(** Source for [convergent_sequences_scale]: vector-space scaling for the
    lattice in Federer 2.5.3, p. 95 Every real scalar is allowed. *)
Lemma convergent_sequences_scale (R : realType) (f : nat -> R) (c : R) :
  convergent_real_sequences f -> convergent_real_sequences (fun n => (c*f n)%R).
Proof.
move=> [a ha]; exists (c*a)%R; exact: (@real_scalar_order_limit R f a c ha).
Qed.

(** Source for [convergent_sequences_add]: vector-space addition for Federer
    2.5.3, p. 95 *)
Lemma convergent_sequences_add (R : realType) (f g : nat -> R) :
  convergent_real_sequences f -> convergent_real_sequences g ->
  convergent_real_sequences (fun n => (f n+g n)%R).
Proof.
move=> [a ha] [b hb]; exists (a+b)%R; exact: (@real_sequence_limit_add R f g a b ha hb).
Qed.

(** Source for [convergent_sequences_subtract]: arbitrary differences in the
    vector space of Federer 2.5.3, p. 95 *)
Lemma convergent_sequences_subtract (R : realType) (f g : nat -> R) :
  convergent_real_sequences f -> convergent_real_sequences g ->
  convergent_real_sequences (fun n => (f n-g n)%R).
Proof.
move=> [a ha] [b hb]; exists (a-b)%R; exact: (@real_sequence_limit_subtract R f g a b ha hb).
Qed.

(** Source for [convergent_sequences_lattice]: the exact closure-only
    lattice of Federer 2.5.3, p. 95 In particular, minimum with any
    nonnegative constant remains convergent. *)
Theorem convergent_sequences_lattice (R : realType) : is_function_lattice (@convergent_real_sequences R).
Proof.
constructor.
- move=> f g; exact: (@convergent_sequences_add R f g).
- move=> c f hc; exact: (@convergent_sequences_scale R f c).
- move=> f g [a ha] [b hb]; exists (Order.min a b).
  exact: (@real_sequence_limit_minimum R f g a b ha hb).
- move=> c f hc [a ha]; exists (Order.min a c).
  exact: (@real_sequence_limit_minimum R f (fun _ => c) a c ha (real_constant_order_limit c)).
- move=> f g hf hg hfg; exact: (@convergent_sequences_subtract R g f hg hf).
Qed.

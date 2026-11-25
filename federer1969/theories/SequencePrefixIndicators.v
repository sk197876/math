(** Federer (1969), 2.5.3, p. 95, last paragraph: independence of increasing
    continuity for the sequence limit functional. These finite-prefix
    indicators increase pointwise to one, although each has sequence limit
    zero. Indices start at zero, corresponding to the book's positive
    integers by n+1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ConvergentSequenceLattice MonotoneDaniellIntegralUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_prefix_indicator]: explicit test sequence verifying
    the counterexample in Federer 2.5.3, p. 95 The value is one through k
    and zero afterward. *)
Definition sequence_prefix_indicator (R : realType) (k n : nat) : R :=
  if (n <= k)%N then 1%R else 0%R.

(** Source for [sequence_prefix_indicator_limit_zero]: each finite prefix
    has limit zero, supporting the counterexample in Federer 2.5.3, p. 95 *)
Lemma sequence_prefix_indicator_limit_zero (R : realType) k :
  extended_order_limit (fun n => (@sequence_prefix_indicator R k n)%:E) 0.
Proof.
have hz n : (k.+1 <= n)%N -> @sequence_prefix_indicator R k n=0%R.
  move=> hn; by rewrite /sequence_prefix_indicator leqNgt hn.
split=> a ha; exists k.+1=> n hn; by rewrite (hz n hn).
Qed.

(** Source for [sequence_prefix_indicator_member]: membership of every
    prefix in the exact lattice of Federer 2.5.3, p. 95 *)
Lemma sequence_prefix_indicator_member (R : realType) k :
  convergent_real_sequences (@sequence_prefix_indicator R k).
Proof. exists 0%R; exact: sequence_prefix_indicator_limit_zero. Qed.

(** Source for [sequence_prefix_indicators_increase_one]: pointwise increase
    to the constant one in the counterexample of Federer 2.5.3, p. 95 *)
Theorem sequence_prefix_indicators_increase_one (R : realType) :
  real_functions_increase_to (@sequence_prefix_indicator R) (fun _ => 1%R).
Proof.
move=> x; split.
- move=> n m hnm; rewrite lee_fin /sequence_prefix_indicator.
  case hxn: (x <= n)%N.
  + have hxm := leq_trans hxn hnm; by rewrite hxm.
  + by case: (x <= m)%N; rewrite ?ler01.
- split=> a ha; exists x=> n hn; by rewrite /sequence_prefix_indicator hn.
Qed.

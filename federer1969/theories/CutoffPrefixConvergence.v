(** Federer (1969), 2.5.10, p. 101: exhaustion of a countable union of
    pieces by its finite prefixes. Positive cutoffs increase pointwise, so
    the Daniell continuity already proved in 2.5.7 applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import SetSequenceDisjointification MonotoneDaniellIntegralUP TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_cutoff_prefix_eventually_equal]: supporting
    pointwise exhaustion in Federer 2.5.10, p. 101. Each
    point entering the union belongs to all sufficiently large prefixes. *)
Lemma scalar_cutoff_prefix_eventually_equal (R : realType) (X : Type)
    (B : nat -> set X) (f : X -> R) x :
  exists N, forall n, (N <= n)%N -> total_scalar_cutoff (set_sequence_prefix B n) f x=
    total_scalar_cutoff (\bigcup_i B i) f x.
Proof.
case: (pselect ((\bigcup_i B i) x))=> [[i _ hx]|hx].
- exists i.+1=> n hn.
  have hp : set_sequence_prefix B n x by exists i.
  have hu : (\bigcup_i B i) x by exists i.
  by rewrite !total_scalar_cutoff_on.
- exists 0%N=> n hn.
  have hp : ~ set_sequence_prefix B n x by move=> [i _ hi]; apply: hx; by exists i.
  by rewrite !total_scalar_cutoff_off.
Qed.

(** Source for [positive_cutoff_prefix_increases]: supporting increasing
    sequence used to finish the density gluing in Federer 2.5.10, p. 101 No
    measurability hypotheses are needed for this pointwise fact. *)
Lemma positive_cutoff_prefix_increases (R : realType) (X : Type)
    (B : nat -> set X) (f : X -> R) :
  (forall x, (0 <= f x)%R) ->
  real_functions_increase_to (fun n => total_scalar_cutoff (set_sequence_prefix B n) f)
    (total_scalar_cutoff (\bigcup_i B i) f).
Proof.
move=> hf x; split.
- move=> n m hnm; case: (pselect (set_sequence_prefix B n x))=> hn.
  + have hm := @set_sequence_prefix_mono X B n m hnm x hn.
    by rewrite !total_scalar_cutoff_on.
  + rewrite (total_scalar_cutoff_off f hn).
    case: (pselect (set_sequence_prefix B m x))=> hm.
    * by rewrite total_scalar_cutoff_on // lee_fin.
    * by rewrite total_scalar_cutoff_off.
- have [N hN] := scalar_cutoff_prefix_eventually_equal B f x.
  split=> a ha; exists N=> n hn; by rewrite hN.
Qed.

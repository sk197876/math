(** Federer (1969), 2.5.3, p. 95, final paragraph: the first three
    hypotheses of 2.5.2 do not imply the fourth. The exact lattice is all
    convergent real sequences, and the functional is their limit.
    Finite-prefix indicators witness failure of increasing continuity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ConvergentSequenceLattice MonotoneDaniellIntegralUP
  SequenceLimitFunctionalUP SequenceLimitFunctionalLaws SequenceLimitFunctionalSealed
  SequencePrefixIndicators RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_limit_not_increasing_continuous]: direct
    independence assertion of Federer 2.5.3, p. 95 Every prefix has
    functional value zero while the pointwise limit has value one. *)
Theorem sequence_limit_not_increasing_continuous (R : realType) (A : (nat -> R) -> R) :
  is_sequence_limit_functional A -> ~ is_monotone_daniell_integral (@convergent_real_sequences R) A.
Proof.
move=> hA hD.
have hmem : convergent_real_sequences (fun _ : nat => (1%R : R)).
  exists 1%R; exact: real_constant_order_limit.
have hi := @monotone_daniell_integral_increases R nat (@convergent_real_sequences R) A hD
  (@sequence_prefix_indicator R) (fun _ => 1%R)
  (@sequence_prefix_indicator_member R) hmem (@sequence_prefix_indicators_increase_one R).
rewrite (sequence_limit_functional_constant hA 1%R) in hi.
have [N hN] := hi.2.1 0 lte01.
have hbad := hN N (leqnn N).
have hz := @sequence_limit_functional_value R A hA (@sequence_prefix_indicator R N) 0%R
  (@sequence_prefix_indicator_limit_zero R N).
by move: hbad; rewrite hz ltxx.
Qed.

(** Source for [convergent_sequence_limit_counterexample]: complete example
    at the end of Federer 2.5.3, p. 95 The sealed witness satisfies all
    three displayed algebra and order conditions, while the fourth condition
    fails. *)
Theorem convergent_sequence_limit_counterexample (R : realType) :
  is_function_lattice (@convergent_real_sequences R) /\
  exists A : (nat -> R) -> R,
    (forall f g, convergent_real_sequences f -> convergent_real_sequences g ->
      A (fun n => (f n+g n)%R)=(A f+A g)%R) /\
    (forall c f, (0 <= c)%R -> convergent_real_sequences f ->
      A (fun n => (c*f n)%R)=(c*A f)%R) /\
    (forall f g, convergent_real_sequences f -> convergent_real_sequences g ->
      function_le f g -> (A f <= A g)%R) /\
    ~ is_monotone_daniell_integral (@convergent_real_sequences R) A.
Proof.
split; first exact: convergent_sequences_lattice.
exists (@SequenceLimitFunctional.value R).
have hA := @SequenceLimitFunctional.laws R.
split; first exact: (@sequence_limit_functional_add R _ hA).
split.
- move=> c f hc; exact: (@sequence_limit_functional_scale R _ hA f c).
- split; first exact: (@sequence_limit_functional_monotone R _ hA).
  exact: (@sequence_limit_not_increasing_continuous R _ hA).
Qed.

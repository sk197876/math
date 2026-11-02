(** Federer (1969), 2.5.14, pp. 107–108: alpha satisfies the countable
    open-cover bound. We use arbitrary countable families and retain the
    original cover indices. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactOpenContentUP CompactOpenContentBasic
  CompactPartitionFunctionalBound FiniteCompactPartitionUP FiniteCompactPartitionSealed CompactFiniteCover
  MonotoneDaniellIntegralUP OpenCoverContentUP ExtendedRealBoundsUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_content_countable_cover]: the inequality
    alpha(W) <= sum alpha(V_n) in Federer 2.5.14, pp. 107–108 Containment in
    the open union suffices, as in 17.39. *)
Theorem compact_open_content_countable_cover (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) :
  hausdorff_space X -> locally_compact (@setT X) ->
  forall W C, open W -> (forall V, C V -> open V) ->
    W `<=` \bigcup_(V in C) V -> a W <= nonnegative_sum C a.
Proof.
move=> hh hl W C hW hC hWC.
apply: (extended_real_supremum_least (ha W hW))=> c [f [[hf [hb hs]] ->]].
have hcov : real_function_support f `<=` \bigcup_(V in C) V.
  move=> x hx; exact: hWC x (hs x hx).
have [F hFC hFK] := @compact_open_finite_cover X [the choiceType of set X] C id
  (real_function_support f) hf.2 hC hcov.
have hF V : V \in F -> open V.
  move=> hV; apply: hC; exact: set_mem (hFC V hV).
pose g := @FiniteCompactPartition.value R X [the choiceType of set X] id F
  (real_function_support f) hh hl hf.2 hF hFK.
have hg := @FiniteCompactPartition.laws R X [the choiceType of set X] id F
  (real_function_support f) hh hl hf.2 hF hFK.
have hbound := @compact_partition_functional_bound R X [the choiceType of set X] A a hA ha
  id F f g hf hb hF hg.
apply: le_trans hbound _; apply: nonnegative_sum_upper=> V hV.
exact: set_mem (hFC V hV).
Qed.

(** Source for [compact_open_content_is_open_cover_content]: all open-cost
    hypotheses needed to conclude that Phi measures X in Federer 2.5.14, p.
    108 The cover estimate actually holds without countability because each
    test support has a finite subcover. *)
Theorem compact_open_content_is_open_cover_content (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) :
  hausdorff_space X -> locally_compact (@setT X) -> is_open_cover_content a.
Proof.
move=> hh hl; constructor.
- move=> V hV; exact: (@compact_open_content_nonnegative R X A a hA ha V hV).
- exact: (@compact_open_content_empty R X A a hA ha).
- move=> W C hW _ hC hWC; exact: (@compact_open_content_countable_cover R X A a hA ha hh hl W C hW hC hWC).
Qed.

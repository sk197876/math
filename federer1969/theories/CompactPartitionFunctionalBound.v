(** Federer (1969), 2.5.14, p. 108, second display: lambda(f) is the sum of
    lambda(g_n f), bounded by the sum of the open costs. The proof depends
    only on the partition's abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  CompactOpenContentUP FiniteCompactPartitionUP FunctionLatticeUP MonotoneDaniellIntegralUP
  DaniellFiniteSums ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_test_partition_product]: each product g_n f is
    admissible for alpha(V_n) in Federer 2.5.14, p. 108 *)
Lemma compact_test_partition_product (R : realType) (X : topologicalType)
    (f g : X -> R) V : compactly_supported_continuous_functions f ->
  (forall x, (0 <= f x <= 1)%R) -> is_compact_open_test_function V g ->
  is_compact_open_test_function V (fun x => (f x*g x)%R).
Proof.
move=> hf hb [hg [hc hs]]; split.
- exact: compact_support_continuous_multiplier hf.1 hg.
- split.
  + move=> x; have [hf0 hf1] := andP (hb x); have [hg0 hg1] := andP (hc x).
    apply/andP; split; first exact: mulr_ge0 hf0 hg0.
    have hh := ler_wpM2l hf0 hg1; rewrite mulr1 in hh; exact: le_trans hh hf1.
  + move=> x hx; apply: hs; exact: real_product_support_right hx.
Qed.

(** Source for [compact_partition_functional_bound]: the finite inequality
    lambda(f) <= sum alpha(V_n) in Federer 2.5.14, p. 108 Zero functions and
    empty finite covers are included. *)
Theorem compact_partition_functional_bound (R : realType) (X : topologicalType) (J : choiceType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) (V : J -> set X) (F : {fset J})
    (f : X -> R) (g : J -> X -> R) :
  compactly_supported_continuous_functions f -> (forall x, (0 <= f x <= 1)%R) ->
  (forall j, j \in F -> open (V j)) ->
  is_finite_compact_partition V F (real_function_support f) g ->
  (A f)%:E <= \sum_(j <- F) a (V j).
Proof.
move=> hf hb hV hp.
pose k j x := (f x*g j x)%R.
have hk j : j \in F -> is_compact_open_test_function (V j) (k j).
  move=> hj; apply: (@compact_test_partition_product R X f (g j) (V j) hf hb).
  split; first exact: (@finite_compact_partition_functions R X J V F (real_function_support f) g hp j hj).
  split; [exact: (@finite_compact_partition_range R X J V F (real_function_support f) g hp j hj)|exact: (@finite_compact_partition_support R X J V F (real_function_support f) g hp j hj)].
have he : f=(fun x => (\sum_(j <- F) k j x)%R).
  apply: funext=> x; rewrite /k -mulr_sumr.
  case: (pselect (real_function_support f x))=> hx.
  + by rewrite (@finite_compact_partition_sum R X J V F (real_function_support f) g hp x hx) mulr1.
  + by rewrite (real_function_zero_off_support hx) mul0r.
have hv : A f=(\sum_(j <- F) A (k j))%R.
  rewrite he; apply: (@monotone_daniell_sequence_sum R X J _ A
    (@compactly_supported_continuous_functions_lattice R X) hA F k
    (@compactly_supported_zero_function R X))=> j hj; exact: (hk j hj).1.
rewrite hv -sumEFin !big_seq; apply: lee_sum=> j hj.
have htest : (A (k j))%:E <= a (V j).
  apply (@extended_real_supremum_upper R _ _ (ha (V j) (hV j hj)) (A (k j))%:E); exists (k j); split=> //; exact: hk hj.
exact htest.
Qed.

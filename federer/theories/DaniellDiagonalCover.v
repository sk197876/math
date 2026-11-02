(** Federer (1969), proof of 2.5.2, p. 92: diagonal finite sums of sequences
    suiting a countable cover. The countable index set is exhausted by
    finite sets through the previously sealed interface; this is the indexed
    form of the printed sums from 1 to n. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralLaws DaniellCoverUP DaniellCoverBasic DaniellFiniteSums
  CountableFiniteExhaustionUP CountableFiniteExhaustionSealed ExtendedRealBoundsUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_diagonal_suits]: the sequence g_n suiting A in
    Federer 2.5.2, p. 92 An arbitrary finite exhaustion replaces the initial
    segment of a numbered countable cover. *)
Lemma daniell_diagonal_suits (R : realType) (X : Type) (J : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (D : set J)
    (C : nat -> {fset J}) (hC : is_countable_finite_exhaustion D C)
    (S : J -> set X) (T : set X) (f : J -> nat -> X -> R) :
  L (fun _ => 0%R) -> T `<=` \bigcup_(j in D) S j ->
  (forall j, D j -> is_daniell_suiting_sequence L (S j) (f j)) ->
  is_daniell_suiting_sequence L T (fun n x => (\sum_(j <- C n) f j n x)%R).
Proof.
move=> h0 hT hf.
have hpos n x : (0 <= \sum_(j <- C n) f j n x)%R.
  rewrite big_seq; apply: sumr_ge0=> j hj.
  exact: ((hf j (finite_exhaustion_subset hC hj)).1 n).2 x.
split.
- move=> n; split; last exact: hpos.
  apply: (@function_lattice_sequence_sum R X J L hL (C n) (fun j => f j n) h0)=> j hj.
  exact: ((hf j (finite_exhaustion_subset hC hj)).1 n).1.
- split.
  + move=> n m hnm x.
    apply: le_trans (_ : (\sum_(j <- C n) f j m x <= \sum_(j <- C m) f j m x)%R).
    * rewrite !big_seq; apply: ler_sum=> j hj.
      exact: (hf j (finite_exhaustion_subset hC hj)).2.1 n m hnm x.
    * apply: finite_nonnegative_real_sum_subset (finite_exhaustion_increasing hC hnm) _=> j hj.
      exact: ((hf j (finite_exhaustion_subset hC hj)).1 m).2 x.
  + move=> x hx r hr.
    have [j hj hxj] := hT x hx.
    have [k hk] := finite_exhaustion_cover hC hj.
    have [n hn] := (hf j hj).2.2 x hxj r hr.
    exists (maxn k n).
    have hjm : j \in C (maxn k n).
      exact: (fsubsetP (finite_exhaustion_increasing hC (leq_maxl k n))) j hk.
    apply: lt_le_trans hn _.
    apply: le_trans ((hf j hj).2.1 n (maxn k n) (leq_maxr k n) x) _.
    apply: finite_nonnegative_real_sum_term hjm _=> i hi.
    exact: ((hf i (finite_exhaustion_subset hC hi)).1 (maxn k n)).2 x.
Qed.

(** Source for [daniell_diagonal_cost_bound]: the displayed upper bound for
    lambda(g_n) in Federer 2.5.2, p. 92 Costs may be infinite; all finite
    diagonal functional values remain real. *)
Lemma daniell_diagonal_cost_bound (R : realType) (X : Type) (J : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (D : set J)
    (C : nat -> {fset J}) (hC : is_countable_finite_exhaustion D C)
    (S : J -> set X) (f : J -> nat -> X -> R) (c : J -> \bar R) :
  L (fun _ => 0%R) ->
  (forall j, D j -> is_daniell_suiting_sequence L (S j) (f j)) ->
  (forall j, D j -> is_daniell_sequence_cost A (f j) (c j)) ->
  forall n, (A (fun x => (\sum_(j <- C n) f j n x)%R))%:E <= nonnegative_sum D c.
Proof.
move=> h0 hf hc n.
have hLn j : j \in C n -> L (f j n).
  move=> hj; exact: ((hf j (finite_exhaustion_subset hC hj)).1 n).1.
rewrite (monotone_daniell_sequence_sum hL hA h0 hLn) -sumEFin.
apply: le_trans (_ : (\sum_(j <- C n) c j) <= nonnegative_sum D c).
- rewrite !big_seq; apply: lee_sum=> j hj.
  apply: (extended_real_supremum_upper (hc j (finite_exhaustion_subset hC hj))).
  by exists n.
- apply: nonnegative_sum_upper=> j hj; exact: (finite_exhaustion_subset hC hj).
Qed.

(** Source for [daniell_cover_countable_suiting_bound]: the countable-cover
    estimate before the infimum approximation in Federer 2.5.2, p. 92 This
    proves the estimate for supplied suiting sequences, before selecting
    costs close to each covering mass. *)
Theorem daniell_cover_countable_suiting_bound (R : realType) (X : Type) (J : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (D : set J) (S : J -> set X)
    (T : set X) (f : J -> nat -> X -> R) (c : J -> \bar R) :
  L (fun _ => 0%R) -> countable D -> T `<=` \bigcup_(j in D) S j ->
  (forall j, D j -> is_daniell_suiting_sequence L (S j) (f j)) ->
  (forall j, D j -> is_daniell_sequence_cost A (f j) (c j)) ->
  mu T <= nonnegative_sum D c.
Proof.
move=> h0 hD hT hf hc.
pose C := @CountableFiniteExhaustion.value J D hD.
have hC : is_countable_finite_exhaustion D C := @CountableFiniteExhaustion.laws J D hD.
pose g n x := (\sum_(j <- C n) f j n x)%R.
have hg : is_daniell_suiting_sequence L T g := daniell_diagonal_suits hL hC h0 hT hf.
have [b hb] := daniell_sequence_cost_exists A g.
apply: le_trans (daniell_cover_lower hm hg hb) _.
apply: (extended_real_supremum_least hb)=> z [n ->].
exact: (@daniell_diagonal_cost_bound R X J L A hL hA D C hC S f c h0 hf hc n).
Qed.

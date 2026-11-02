(** Federer (1969), proof of 2.5.2, p. 93, first paragraph: split a suiting
    sequence into min(g_n,h) and its positive remainder. The supporting
    statements isolate the cutoff's zero and one sets before its application
    to level sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  DaniellCoverUP DaniellCoverBasic ExtendedRealBoundsUP ExtendedFiniteIncreasingBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_capped_remainder_monotone]: scalar support for
    g_n-min(g_n,h) increasing in Federer 2.5.2, p. 93 *)
Lemma real_capped_remainder_monotone (R : realType) (a b h : R) :
  (a <= b)%R -> (a-Order.min a h <= b-Order.min b h)%R.
Proof.
move=> hab; case: (leP a h)=> hah.
- rewrite subrr subr_ge0; by rewrite ge_min lexx.
- have hhb : (h <= b)%R := le_trans (ltW hah) hab.
  by rewrite (min_r hhb) lerD2r.
Qed.

(** Source for [daniell_suiting_cutoff]: the sequence k_n suiting T
    intersect {h= 1} in Federer 2.5.2, p. 93 No measurability of the cutoff
    is required at this stage. *)
Lemma daniell_suiting_cutoff (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (T : set X)
    (g : nat -> X -> R) (h : X -> R) :
  is_daniell_suiting_sequence L T g -> positive_function_lattice L h ->
  is_daniell_suiting_sequence L (T `&` [set x | h x= 1%R])
    (fun n x => Order.min (g n x) (h x)).
Proof.
move=> hs hh; split.
- move=> n; split; first exact: (function_lattice_minimum hL (hs.1 n).1 hh.1).
  by move=> x; rewrite le_min (hs.1 n).2 hh.2.
- split.
  + move=> n m hnm x; rewrite le_min; apply/andP; split.
    * apply: le_trans (_ : (g n x <= g m x)%R); last exact: hs.2.1 n m hnm x.
      by rewrite ge_min lexx.
    * by rewrite ge_min lexx orbT.
  + move=> x [hx he] r hr; have [n hn] := hs.2.2 x hx r hr.
    exists n; by rewrite he lt_min hn hr.
Qed.

(** Source for [daniell_suiting_remainder]: g_n-k_n suits T intersect {h=0}
    in Federer 2.5.2, p. 93 The ordered subtraction and pointwise
    nonnegativity hypotheses are retained. *)
Lemma daniell_suiting_remainder (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (T : set X)
    (g : nat -> X -> R) (h : X -> R) :
  is_daniell_suiting_sequence L T g -> positive_function_lattice L h ->
  is_daniell_suiting_sequence L (T `&` [set x | h x=0%R])
    (fun n x => (g n x-Order.min (g n x) (h x))%R).
Proof.
move=> hs hh; split.
- move=> n; split.
  + apply: (@function_lattice_ordered_difference R X L hL
      (fun x => Order.min (g n x) (h x)) (g n)
      (function_lattice_minimum hL (hs.1 n).1 hh.1) (hs.1 n).1).
    by move=> x; rewrite ge_min lexx.
  + by move=> x; rewrite subr_ge0 ge_min lexx.
- split.
  + move=> n m hnm x; exact: real_capped_remainder_monotone (hs.2.1 n m hnm x).
  + move=> x [hx he] r hr; have [n hn] := hs.2.2 x hx r hr.
    exists n; by rewrite he min_r ?(hs.1 n).2 // subr0.
Qed.

(** Source for [daniell_split_cost_bound]: the sum of the two limiting costs
    is at most the original cost in Federer 2.5.2, p. 93 The extended-real
    limits may be infinite. The proof passes through each increasing limit
    using the previously proved finite-sum bound, avoiding undefined
    infinite subtraction. *)
Lemma daniell_split_cost_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (S T U : set X)
    (g k r : nat -> X -> R) (c d e : \bar R) :
  is_daniell_suiting_sequence L S g -> is_daniell_suiting_sequence L T k ->
  is_daniell_suiting_sequence L U r ->
  is_daniell_sequence_cost A g c -> is_daniell_sequence_cost A k d ->
  is_daniell_sequence_cost A r e ->
  (forall n x, g n x=(k n x+r n x)%R) -> d+e <= c.
Proof.
move=> hg hk hr hc hd he hsum.
have hkd := daniell_sequence_cost_limit hA hk hd.
have hre := daniell_sequence_cost_limit hA hr he.
have hkp n : 0 <= (A (k n))%:E.
  rewrite lee_fin; exact: (monotone_daniell_integral_nonnegative hL hA (hk.1 n).1 (hk.1 n).2).
have hrp n : 0 <= (A (r n))%:E.
  rewrite lee_fin; exact: (monotone_daniell_integral_nonnegative hL hA (hr.1 n).1 (hr.1 n).2).
have hep := daniell_sequence_cost_nonnegative hL hA hr he.
apply: (@extended_nonnegative_limit_add_bound R (fun n => (A (k n))%:E) d e c hkp hkd.2 hep)=> n.
rewrite addeC.
apply: (@extended_nonnegative_limit_add_bound R (fun m => (A (r m))%:E) e (A (k n))%:E c hrp hre.2 (hkp n))=> m.
pose N := maxn n m.
have hkn : (A (k n))%:E <= (A (k N))%:E := hkd.1 n N (leq_maxl n m).
have hrm : (A (r m))%:E <= (A (r N))%:E := hre.1 m N (leq_maxr n m).
apply: le_trans (leeD hrm hkn) _.
have hgN : g N=(fun x => (k N x+r N x)%R) by apply: funext; exact: hsum.
rewrite addeC -EFinD -(monotone_daniell_integral_add hA (hk.1 N).1 (hr.1 N).1) -hgN.
apply: (extended_real_supremum_upper hc); by exists N.
Qed.

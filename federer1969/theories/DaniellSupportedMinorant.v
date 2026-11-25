(** Federer (1969), proof of 2.5.2, p. 92, final paragraph: a positive
    lattice function bounded by one on S and zero outside S has functional
    value at most phi(S). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP DaniellCoverUP
  ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_suiting_minimum_increases]: the sequence h_n =
    min(f_n,g) increases to g in Federer 2.5.2, p. 92, last paragraph *)
Lemma daniell_suiting_minimum_increases (R : realType) (X : Type)
    (L : set (X -> R)) (S : set X) (f : nat -> X -> R) (g : X -> R) :
  is_daniell_suiting_sequence L S f -> function_nonnegative g ->
  (forall x, S x -> (g x <= 1)%R) -> (forall x, ~ S x -> g x=0%R) ->
  real_functions_increase_to (fun n x => Order.min (f n x) (g x)) g.
Proof.
move=> hs hg hb hz x; split.
- move=> n m hnm; rewrite lee_fin le_min; apply/andP; split.
  + apply: le_trans (_ : (f n x <= f m x)%R); last exact: hs.2.1 n m hnm x.
    by rewrite ge_min lexx.
  + by rewrite ge_min lexx orbT.
- split.
  + move=> a ha; case: a ha=> [r| |] ha.
    * have hrg : (r < g x)%R by move: ha; rewrite lte_fin.
      case: (pselect (S x))=> hx.
      -- have hr1 : (r < 1)%R := lt_le_trans hrg (hb x hx).
         have [N hN] := hs.2.2 x hx r hr1.
         exists N=> n hn; rewrite lte_fin lt_min hrg andbT.
         exact: lt_le_trans hN (hs.2.1 N n hn x).
      -- exists 0%N=> n _; rewrite (hz x hx) in hrg *.
         rewrite min_r ?lte_fin //.
         exact: (hs.1 n).2 x.
    * by move: ha; rewrite ltNge leey.
    * exists 0%N=> n _; exact: ltNyr.
  + move=> b hb'; exists 0%N=> n _; apply: le_lt_trans _ hb'.
    by rewrite lee_fin ge_min lexx orbT.
Qed.

(** Source for [daniell_supported_minorant_bound]: the inequality lambda(g)
    <= phi(S) in Federer 2.5.2, p. 92, final paragraph The proof uses only
    the envelope specification and increasing continuity, and does not
    presuppose measurability of g. *)
Theorem daniell_supported_minorant_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (S : set X) (g : X -> R) :
  positive_function_lattice L g -> (forall x, S x -> (g x <= 1)%R) ->
  (forall x, ~ S x -> g x=0%R) -> (A g)%:E <= mu S.
Proof.
move=> hg hb hz; apply: (daniell_cover_greatest hm)=> f c hs hc.
pose h n x := Order.min (f n x) (g x).
have hLh n : L (h n) := function_lattice_minimum hL (hs.1 n).1 hg.1.
have hh : real_functions_increase_to h g := daniell_suiting_minimum_increases hs hg.2 hb hz.
have hAh := monotone_daniell_integral_increases hA hLh hg.1 hh.
apply: extended_order_limit_upper_bound hAh.2 _=> n.
apply: le_trans (_ : (A (f n))%:E <= c).
- rewrite lee_fin; apply: (@monotone_daniell_integral_monotone R X L A hA (h n) (f n) (hLh n) (hs.1 n).1).
  by move=> x; rewrite /h ge_min lexx.
- apply: (extended_real_supremum_upper hc); by exists n.
Qed.

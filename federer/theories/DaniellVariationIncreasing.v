(** Federer (1969), 2.5.5, p. 97: for h_n increasing to g and 0 <= k <= g,
    min(h_n,k) increases to k. Continuity of mu on that sequence identifies
    the supremum of mu+(h_n) with mu+(g). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariationBounds
  MonotoneDaniellIntegralUP RealSequenceLimitArithmetic RealScalarOrderLimits
  ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealOrderLimit ExtendedRealLimitBounds ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_increasing_functions_below_limit]: supporting pointwise
    bound h_n <= g used in Federer 2.5.5, p. 97 *)
Lemma real_increasing_functions_below_limit (R : realType) (X : Type)
    (h : nat -> X -> R) (g : X -> R) :
  real_functions_increase_to h g -> forall n, function_le (h n) g.
Proof.
move=> hg n x.
have hs := extended_increasing_limit_supremum (hg x).
have hb : (h n x)%:E <= (g x)%:E.
  apply: (extended_real_supremum_upper hs); by exists n.
by move: hb; rewrite lee_fin.
Qed.

(** Source for [real_increasing_functions_minimum]: exact pointwise
    convergence min(h_n,k) increasing to k in Federer 2.5.5, p. 97 Only k <=
    g is needed for this scalar fact. *)
Lemma real_increasing_functions_minimum (R : realType) (X : Type)
    (h : nat -> X -> R) (g k : X -> R) :
  real_functions_increase_to h g -> function_le k g ->
  real_functions_increase_to (fun n x => Order.min (h n x) (k x)) k.
Proof.
move=> hg hkg x; split.
- move=> n m hnm; rewrite lee_fin le_min; apply/andP; split.
  + have hm : (h n x <= h m x)%R by have := (hg x).1 n m hnm; rewrite lee_fin.
    apply: le_trans (_ : (h n x <= h m x)%R)=> //.
    by rewrite ge_min lexx.
  + by rewrite ge_min lexx orbT.
- have hh := @real_sequence_limit_minimum R (fun n => h n x) (fun _ => k x)
    (g x) (k x) (hg x).2 (@real_constant_order_limit R (k x)).
  by rewrite min_r // in hh.
Qed.

(** Source for [daniell_positive_variation_increases]: increasing continuity
    of mu+ in Federer 2.5.5, p. 97 The original values mu(min(h_n,k)) need
    not be monotone, and only their ordinary convergence is used to bound
    mu(k) by the limiting supremum. *)
Theorem daniell_positive_variation_increases (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (h : nat -> X -> R) (g : X -> R) :
  (forall n, positive_function_lattice L (h n)) -> positive_function_lattice L g ->
  real_functions_increase_to h g ->
  extended_increases_to (fun n => (P (h n))%:E) (P g)%:E.
Proof.
move=> hh hg hinc.
pose s := extended_real_sup [set t : \bar R | exists n, t=(P (h n))%:E].
have hmono n m : (n <= m)%N -> (P (h n))%:E <= (P (h m))%:E.
  move=> hnm; rewrite lee_fin.
  apply: (@daniell_positive_variation_monotone R X L A P hP _ _ (hh n) (hh m))=> x.
  by have := (hinc x).1 n m hnm; rewrite lee_fin.
have hs := @extended_increasing_limit R (fun n => (P (h n))%:E) hmono.
have hup : s <= (P g)%:E.
  apply: extended_real_sup_least=> t [n ->]; rewrite lee_fin.
  apply: (@daniell_positive_variation_monotone R X L A P hP _ _ (hh n) hg).
  exact: (@real_increasing_functions_below_limit R X h g hinc n).
have hlo : (P g)%:E <= s.
  apply: (extended_real_supremum_least (hP g hg))=> t [k [hk ->]].
  pose u n x := Order.min (h n x) (k x).
  have hu n : L (u n) := function_lattice_minimum hL (hh n).1 hk.1.
  have huc := @real_increasing_functions_minimum R X h g k hinc hk.2.2.
  have hAu := @daniell_integral_increasing_continuity R X L A hA u k hu hk.1 huc.
  apply: (@extended_order_limit_upper_bound R (fun n => (A (u n))%:E) (A k)%:E s hAu)=> n.
  apply: le_trans (_ : (P (h n))%:E <= s).
  - rewrite lee_fin; apply: (@daniell_positive_variation_upper R X L A P hP _ (u n) (hh n)).
    split; first exact: hu n.
    split=> x; [by rewrite /u le_min (hh n).2 hk.2.1|by rewrite /u ge_min lexx].
  - apply: extended_real_sup_upper; by exists n.
have he : s=(P g)%:E by apply/eqP; rewrite eq_le hup hlo.
by rewrite /s in he; rewrite he in hs.
Qed.

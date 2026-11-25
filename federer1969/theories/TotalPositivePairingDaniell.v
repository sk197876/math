(** Federer (1969), 2.5.7, p. 99: the integral pairing with the nonnegative
    density k+ + r is increasing-continuous on the positive lattice. We
    prove it from the existing monotone convergence theorem, with actual
    product summability explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP MonotoneDaniellIntegralUP SummableRealFunctionUP
  TotalScalarPairingValue RealIntegralIncreasingContinuity RealScalarOrderLimits ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_weight_increasing_functions]: supporting
    preservation of pointwise increasing limits when multiplying by the
    nonnegative density in Federer 2.5.7, p. 99 The weight is finite at
    every point; zero weights are included. *)
Lemma nonnegative_weight_increasing_functions (R : realType) (X : Type)
    (f : nat -> X -> R) (g k : X -> R) :
  (forall x, (0 <= k x)%R) -> real_functions_increase_to f g ->
  real_functions_increase_to (fun n x => (f n x*k x)%R) (fun x => (g x*k x)%R).
Proof.
move=> hk hf x; split.
- move=> n m hnm; rewrite lee_fin.
  apply: (ler_wpM2r (hk x)).
  have hh := (hf x).1 n m hnm; by move: hh; rewrite lee_fin.
- have hh := @real_scalar_order_limit R (fun n => f n x) (g x) (k x) (hf x).2.
  have he : (fun n => (k x*f n x)%:E)=(fun n => (f n x*k x)%:E).
    by apply: funext=> n; rewrite mulrC.
  by rewrite he mulrC in hh.
Qed.

(** Source for [nonnegative_pairing_monotone_daniell]: full monotone Daniell
    laws for the nonnegative integral pairing used in Federer 2.5.7, p. 99
    The common lattice need not contain constants or be nonempty. Product
    summability is subsequently supplied by the conjugate-space Holder
    estimates, rather than postulated as a global axiom. *)
Theorem nonnegative_pairing_monotone_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (k : X -> R) :
  is_function_lattice L -> (forall x, (0 <= k x)%R) ->
  (forall f, L f -> summable_real_functions mu (fun x => (f x*k x)%R)) ->
  is_monotone_daniell_integral L (fun f => total_scalar_pairing mu f k).
Proof.
move=> hL hk hprod; constructor.
- move=> f g hf hg.
  exact: (@total_scalar_pairing_add_left R X mu hm f g k (hprod f hf) (hprod g hg)).
- move=> c f hc hf.
  exact: (@total_scalar_pairing_scale_left R X mu hm f k c (hprod f hf)).
- move=> f g hf hg hfg.
  exact: (@total_scalar_pairing_monotone_left R X mu hm f g k (hprod f hf) (hprod g hg) hk hfg).
- move=> f g hf hg hfg.
  apply: (@real_integral_increasing_continuity R X mu hm
    (fun n x => (f n x*k x)%R) (fun x => (g x*k x)%R)
    (fun n => total_scalar_pairing mu (f n) k) (total_scalar_pairing mu g k)).
  + move=> n; exact: (@total_scalar_pairing_specification R X mu (f n) k (hprod _ (hf n))).
  + exact: (@total_scalar_pairing_specification R X mu g k (hprod _ hg)).
  + exact: (@nonnegative_weight_increasing_functions R X f g k hk hfg).
Qed.

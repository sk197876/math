(** Private existence proof for Euler Gamma in Federer
    (1969), 3.2.13, p. 250. The graph
    consists of the actual positive-domain integral values.
    Finiteness, positivity and uniqueness have been proved
    before introducing any opaque selected function. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal.
From Federer Require Import EulerGammaUP EulerGammaPositive PartialFunctionUP
  MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euler_gamma_exists]: proved existence of
    the positive finite integral defining Gamma in
    Federer 3.2.13, p. 250. This private
    witness is to be hidden behind an opaque signature;
    downstream proofs use only is_euler_gamma. *)
Theorem euler_gamma_exists (R:realType):
  exists G:partial_function R R,is_euler_gamma G.
Proof.
pose rel (s a:R):=(0<s)%R /\
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set x:R|(0<x)%R]
    (real_total_integrand (euler_gamma_integrand s)) a%:E.
have hu s a b:rel s a ->rel s b ->a=b.
  move=>[_ ha] [_ hb].
  have he:=measure_integral_unique ha hb.
  exact (EFin_inj he).
pose G:=@Build_partial_function R R rel hu.
exists G; constructor.
- by move=>s a.
- move=>s hs; have [a [ha hI]]:=euler_gamma_positive_finite_integral hs.
  exists a; by split.
- move=>s a [hs hI].
  have [b [hb hIb]]:=euler_gamma_positive_finite_integral hs.
  have he:a=b:=hu s a b (conj hs hI) (conj hs hIb).
  by rewrite he.
Qed.

(** Federer (1969), proof of 2.5.2, p. 93: lambda(f)=integral(f) for f in
    L+, after the two increasing limits. The final cutoff limit is taken
    along the cofinal reciprocal sequence 1/(n+1). Finiteness of the
    integral follows from the real functional value; it is not an extra
    hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLayers MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellPositiveIntegral DaniellPositiveIncreasingIntegral
  DaniellTailIntegralBound DaniellTailFunctionalBound RealLatticeTruncationLimits
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralBounds ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_positive_lattice_representation]: the equality for
    every f in L+ in Federer 2.5.2, p. 93 The integral witness is obtained
    from measurability and positivity and then identified with the supplied
    functional value. *)
Theorem daniell_positive_lattice_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) :
  positive_function_lattice L f -> is_measure_integral mu (real_total_integrand f) (A f)%:E.
Proof.
move=> hf; pose u n := real_lattice_tail f (((n.+1)%:R : R)^-1).
have he n : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
have hu n : positive_function_lattice L (u n) := real_lattice_tail_member hL hf.1 (ltW (he n)).
have hinc : real_functions_increase_to u f := real_reciprocal_truncation_tails_increase hf.2.
have hIlim := daniell_positive_increasing_integral_values hL hA hm hu hf hinc.
have hAlim := @monotone_daniell_integral_increases R X L A hA u f (fun n => (hu n).1) hf.1 hinc.
have hup : measure_lower_integral mu (real_total_integrand f) <= (A f)%:E.
  apply: (extended_order_limit_upper_bound hIlim.2)=> n.
  exact: (@daniell_tail_integral_upper_bound R X L A hL hA mu hm f (((n.+1)%:R)^-1)%R hf (he n)).
have hlo : (A f)%:E <= measure_lower_integral mu (real_total_integrand f).
  apply: (extended_order_limit_upper_bound hAlim.2)=> n.
  exact: (@daniell_tail_functional_lower_bound R X L A hL hA mu hm f (((n.+1)%:R)^-1)%R hf (he n)).
have eqI : measure_lower_integral mu (real_total_integrand f)=(A f)%:E.
  by apply/eqP; rewrite eq_le hup hlo.
have hi := (daniell_positive_lattice_integral hL hA hm hf).1.
by rewrite eqI in hi.
Qed.

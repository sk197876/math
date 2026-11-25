(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 333–334:
    the actual zero set of the chosen
    holomorphic cut is a finite holomorphic variety
    on its original domain. Keep the one
    original equation and no arbitrary extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric HolomorphicUP NormAnalyticLocal FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_single_equation]:
    the actual exceptional one-equation variety of
    the full-dimensional case in 3.4.12, p. 339, extending 3.4.8(11), p. 333,
    also used for the original prefix cut on p. 334. *)
Theorem finite_holomorphic_single_equation (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U:set X) (phi:X->(ComplexScalars.C R)^o):
  @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) U phi ->
  @is_finite_holomorphic_variety R X NX hNX U (U `&` [set x|phi x=0]).
Proof.
move=>hPhi;split;first exact:norm_analytic_domain_open hPhi.1.
exists (Finite.clone 'I_1 _),(fun _=>phi);split;first by move=>_.
move=>x;split.
- move=>[hx hZero];split;first exact:hx.
  by move=>_.
- move=>[hx hZero];split;first exact:hx.
  exact:hZero ord0.
Qed.

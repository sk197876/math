(** Federer (1969), 3.4.8(11), pp. 333–334:
    the actual zero set of the chosen
    analytic cut is a finite analytic variety
    on its original domain. Keep the one
    original equation and no arbitrary extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticLocal FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_single_equation]:
    the actual exceptional one-equation variety of
    the full-dimensional case in 3.4.8(11), p. 333,
    also used for the original prefix cut on p. 334. *)
Theorem finite_analytic_single_equation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) (phi:X->R^o):
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) U phi ->
  @is_finite_analytic_variety R X NX hNX U (U `&` [set x|phi x=0]).
Proof.
move=>hPhi;split;first exact:norm_analytic_domain_open hPhi.
exists (Finite.clone 'I_1 _),(fun _=>phi);split;first by move=>_.
move=>x;split.
- move=>[hx hZero];split;first exact:hx.
  by move=>_.
- move=>[hx hZero];split;first exact:hx.
  exact:hZero ord0.
Qed.

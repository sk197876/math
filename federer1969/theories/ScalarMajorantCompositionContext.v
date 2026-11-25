(** Federer (1969), 3.1.24, p. 240: the scalar
    quadratic inverse and rational forward map give an actual
    smooth composition equal to the identity near zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormRegularity NormAnalyticUP ScalarAnalyticFraction
  ScalarInverseMajorant ScalarInverseMajorantIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_majorant_composition_context]: the
    scalar specialization used to identify lambda_p in Federer
    3.1.24, p. 240. The analytic inverse provides an
    actual smooth neighbourhood V of zero. On the exact
    composite domain V intersect F inverse(domain G), both
    formulae are defined and G composed with F is the identity.
    That domain contains zero. No identity at a pole is assumed. *)
Theorem scalar_majorant_composition_context (R:realType) (b g:R) :
  0<b -> 0<g -> exists V:R^o->Prop,
    V 0 /\ (forall x,V x -> scalar_inverse_majorant_domain b x) /\
    norm_class_all_orders (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
      V (scalar_inverse_majorant b g) /\
    scalar_analytic_fraction_domain g (scalar_inverse_majorant b g 0) /\
    forall x,V x -> scalar_analytic_fraction_domain g (scalar_inverse_majorant b g x) ->
      scalar_forward_majorant b g (scalar_inverse_majorant b g x)= x.
Proof.
move=>hb hg.
have [V [c [hV0 [hVD [hc hbound]]]]]:=@scalar_inverse_majorant_analytic_zero R b g hb hg.
exists V; split; first exact hV0.
split; first exact hVD.
split; first exact hc.
split.
- rewrite (scalar_inverse_majorant_zero g hb); exact: scalar_analytic_fraction_zero_domain.
- move=>x hx hdom; exact (scalar_majorant_right_inverse hb hg (hVD x hx) hdom).
Qed.

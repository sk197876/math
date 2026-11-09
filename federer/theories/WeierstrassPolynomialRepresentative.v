(** Federer (1969), 3.4.6(1), p. 322: literal
    finite transverse expressions give the original actual
    polynomial remainder law. This supports concrete examples. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP
  WeierstrassTransverseUP WeierstrassDivisionUP WeierstrassFiniteRemainderVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_polynomial_representative]: a
    finite expression of distinguished degree below k has
    every required actual derivative zero, 3.4.6(1),
    p. 322. No formal derivative or abstract
    vanishing conclusion is assumed for the example. *)
Theorem weierstrass_polynomial_representative (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (C:nat->X->R) (f:analytic_representative_type hNX (0:X)):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    setT (analytic_representative_value f) ->
  analytic_representative_value f=(fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))) ->
  @is_directional_polynomial_germ R X NX hNX k v (analytic_germ f).
Proof.
move=>hSplit hf hValues.
exists f;split;first reflexivity.
exists setT;split;first exact:Logic.I.
split;first exact:hf.
rewrite hValues.
apply:(@weierstrass_finite_remainder_vanishing R X K NX NK hNX v xi inclusion projection k C setT hSplit).
by rewrite -hValues.
Qed.

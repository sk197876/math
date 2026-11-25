(** Federer (1969), 3.4.8(6), p. 329:
    actual pointed pullback preserves the original
    germ value at the corresponding centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws AnalyticGermRing
  AnalyticGermValueUP AnalyticGermValueSealed PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_analytic_pullback_centre_value]:
    coordinate pullback at zero preserves the zero
    centre value used to choose the positive
    derivative order, 3.4.8(6), p. 329. *)
Theorem pointed_analytic_pullback_centre_value (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (a:X) (b:Y) (u:X->Y)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback u P ->u a = b ->forall beta,
    @AnalyticGermValue.map R X NX hNX a (P beta) = @AnalyticGermValue.map R Y NY hNY b beta.
Proof.
move=>hP hCentre beta.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b beta.
have [g [hG hValues]]:=hP f.
by rewrite hG (@AnalyticGermValue.laws R X NX hNX a g)
  (@AnalyticGermValue.laws R Y NY hNY b f) hValues hCentre.
Qed.

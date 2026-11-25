(** Federer (1969), 3.4.4, p. 318: quantitative
    positive-power cutoffs for continuity and flat Whitney jets. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerContinuity RealPowerSuccessor
  RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holder_positive_power_cutoff]: the smallness
    of a positive power of the source distance used
    twice in 3.4.4, p. 318: continuity and
    the vanishing Whitney quotient. The cutoff is an
    existence witness; no modulus of continuity is assumed. *)
Lemma holder_positive_power_cutoff (R:realType) (C q e:R):
  0<C ->0<q ->0<e ->exists delta:R,0<delta /\
    forall d:R,0<=d ->d<=delta ->C*real_power d q<=e.
Proof.
move=>hC hQ hE.
have hDiv:0<e/C by rewrite divr_gt0.
pose delta:=real_power (e/C) q^-1.
have hDelta:0<delta:=@real_power_strictly_positive R (e/C) q^-1 hDiv.
have hValue:real_power delta q=e/C.
  by rewrite /delta real_power_inverse_power ?ltW.
exists delta;split=>// d hd hSmall.
have hBound:=@real_power_monotone R d delta q hd hSmall hQ.
rewrite hValue in hBound.
have h:=ler_wpM2l (ltW hC) hBound.
have hCancel:(C*(e/C):R)=e by rewrite mulrC divfK ?gt_eqF.
by rewrite hCancel in h.
Qed.

(** Source for [holder_power_natural_quotient]: the
    identity behind |phi(u)-phi(v)|/|u-v|^k tending
    to zero when k<alpha/beta, 3.4.4, p. 318.
    Positive distances and the exact natural Taylor order
    make cancellation legitimate, including order zero. *)
Lemma holder_power_natural_quotient (R:realType) (d p:R) k:
  0<d ->real_power d p*d^-(k)=real_power d (p-k%:R).
Proof.
move=>hD.
have hPower:0<d^+k by rewrite exprn_gt0.
have hNe:d^+k!=0 by rewrite gt_eqF.
have hExponent:(p-k%:R+k%:R:R)=p by ring.
have hExpansion:=@real_power_add_exponents_positive R d (p-k%:R) k%:R hD.
rewrite hExponent (@real_power_natural_exponent R d k (ltW hD)) in hExpansion.
by rewrite hExpansion -mulrA mulfV // mulr1.
Qed.

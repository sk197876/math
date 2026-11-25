(** Federer (1969), 3.2.28(3),(5), pp. 266–267:
    the Jacobian factor written with sqrt 2 agrees
    with the printed real power 2^(k/2). *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerSuccessor RealPowerNaturalHausdorff EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_positive_square_root]: the
    positive square-root interpretation of the half power,
    supporting Federer 3.2.28(3),(5), pp. 266–267.
    Uniqueness follows from the nonnegative root laws. *)
Lemma real_power_positive_square_root (R:realType) (x:R):
  0<x ->real_power x (1/2)=Num.sqrt x.
Proof.
move=>hx.
have h0:=real_power_nonnegative x (1/2).
have hSquare:(real_power x (1/2))^+2=x.
  have h2:(0<(2:R)) by rewrite ltr0n.
  rewrite -(@real_power_natural_exponent R (real_power x (1/2)) 2 h0)
    (@real_power_positive_iterate R x (1/2) 2 (ltW hx) (positive_real_half R) h2).
  have hHalf:(1/2:R)*2= 1 by rewrite divfK ?pnatr_eq0.
  by rewrite hHalf real_power_one_exponent //; exact:ltW hx.
have h:=congr1 Num.sqrt hSquare.
by rewrite sqrtr_sqr ger0_norm in h.
Qed.

(** Source for [real_power_half_natural]: the coefficient
    equality (sqrt x)^k=x^(k/2), used with x=2
    in Federer 3.2.28(3),(5), pp. 266–267.
    The zero exponent is retained. *)
Lemma real_power_half_natural (R:realType) (x:R) k:
  0<x ->real_power x (k%:R/2)=(Num.sqrt x)^+k.
Proof.
move=>hx; elim:k=>[|k IH].
- by rewrite mul0r real_power_zero_exponent expr0.
- have hExponent:(k.+1)%:R/2=k%:R/2+(1/2:R).
    by rewrite -addn1 natrD mulrDl.
  rewrite hExponent real_power_add_exponents_positive // IH
    (real_power_positive_square_root hx) exprS mulrC.
  reflexivity.
Qed.

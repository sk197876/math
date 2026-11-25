(** Federer (1969), 3.4.6, pp. 322–324: the
    original finite transverse expression is a literal
    polynomial on each distinguished affine line. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP WeierstrassTransverseUP WeierstrassTransverseLaws
  WeierstrassFiniteShiftExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_finite_remainder_line]: the
    original projection is constant on every distinguished line,
    and xi increases by its line parameter, as used in
    3.4.6, pp. 322–324. *)
Lemma weierstrass_finite_remainder_line (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (v:X) (xi:Hom X R^o)
    (inclusion:Hom K X) (projection:Hom X K) k (C:nat->X->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->forall a t,
  (\sum_(i<k) (xi (a+t*:v))^+i*C i (inclusion (projection (a+t*:v))))=
    \sum_(i<k) (xi a+t)^+i*C i (inclusion (projection a)).
Proof.
move=>hSplit a t;apply:eq_bigr=>i _.
have hXi:xi (a+t*:v)=xi a+t.
  rewrite addrC.
  have hLinear:xi (t*:v+a)=t*xi v+xi a:=hom_linear xi t v a.
  by rewrite hLinear (weierstrass_transverse_functional_value hSplit) mulr1 addrC.
have hProjection:projection (a+t*:v)=projection a.
  rewrite addrC (hom_linear projection t v a).
  by rewrite (weierstrass_projection_direction_zero hSplit) scaler0 add0r.
by rewrite hXi hProjection.
Qed.

(** Source for [weierstrass_finite_remainder_transverse_line]:
    at an original transverse centre the finite line
    coefficients are exactly the original fields C_i,
    supporting 3.4.6, pp. 322–324. *)
Lemma weierstrass_finite_remainder_transverse_line (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (v:X) (xi:Hom X R^o)
    (inclusion:Hom K X) (projection:Hom X K) k (C:nat->X->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->forall z t,
  (\sum_(i<k) (xi (inclusion z+t*:v))^+i*C i (inclusion (projection (inclusion z+t*:v))))=
    \sum_(i<k) t^+i*C i (inclusion z).
Proof.
move=>hSplit z t;rewrite (@weierstrass_finite_remainder_line R X K NX NK v xi inclusion projection k C hSplit).
by rewrite (weierstrass_transverse_kernel hSplit) add0r (weierstrass_transverse_left_inverse hSplit).
Qed.

(** Source for [weierstrass_finite_remainder_shifted_line]:
    the same finite degree bound holds at every original
    centre, supporting the all-nearby-point derivative condition
    in 3.4.6(1), pp. 321–322. *)
Theorem weierstrass_finite_remainder_shifted_line (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (v:X) (xi:Hom X R^o)
    (inclusion:Hom K X) (projection:Hom X K) k (C:nat->X->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->forall a,
  exists b:nat->R,forall t,
    (\sum_(i<k) (xi (a+t*:v))^+i*C i (inclusion (projection (a+t*:v))))=
      \sum_(i<k) t^+i*b i.
Proof.
move=>hSplit a.
exists (fun n=>\sum_(i<k | (n<=i)%N) ('C(i,n))%:R*(xi a)^+(i-n)*C i (inclusion (projection a)))=>t.
rewrite (@weierstrass_finite_remainder_line R X K NX NK v xi inclusion projection k C hSplit).
exact:(@weierstrass_finite_shift_expansion R k (xi a) t
  (fun i=>C i (inclusion (projection a)))).
Qed.

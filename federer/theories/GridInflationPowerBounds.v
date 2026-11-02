(** Federer (1969), 3.2.38, p. 275: uniform constants for
    the affine-tube inflation factor 1+m/v. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import NaturalPowerIncrementBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grid_inflation_power_upper_bound]: supporting the
    uniform xi constant in Federer 3.2.38, p. 275. For v>=1,
    every inflation power of degree at most n is bounded by
    (1+m)^n, independently of the radius and source cube. *)
Lemma grid_inflation_power_upper_bound (R:realType) (v:R) m q n:
  1<=v ->(q<=n)%N ->(1+m%:R/v)^+q<=(1+m%:R)^+n.
Proof.
move=>hv1 hqn.
have hv:0<v:=lt_le_trans ltr01 hv1.
have ht0:0<=v^-1 by rewrite invr_ge0; exact:ltW hv.
have ht1:v^-1<=1 by rewrite invf_le1.
have hs0:0<=m%:R/v:=mulr_ge0 (ler0n R m) ht0.
have hsBound:m%:R/v<=m%:R.
  have h:=ler_wpM2l (ler0n R m) ht1; by rewrite mulr1 in h.
have hA:0<=1+m%:R/v:=addr_ge0 ler01 hs0.
have hB:1<=1+(m%:R:R) by rewrite lerDl ler0n.
have hAB:1+m%:R/v<=1+m%:R by rewrite lerD2l.
have hPower k:(1+m%:R/v)^+k<=(1+m%:R)^+k.
  elim:k=>[|k hk]; first by rewrite !expr0.
  rewrite !exprS; exact:ler_pM hA (exprn_ge0 _ hA) hAB hk.
apply:le_trans (hPower q) _.
exact:(@ler_weXn2l R (1+m%:R) hB q n hqn).
Qed.

(** Source for [grid_inflation_power_increment_bound]: supporting
    the top-Jacobian inflation error in Federer 3.2.38, p. 275.
    A finite geometric sum supplies a constant independent of v;
    degree zero has exactly zero increment. *)
Lemma grid_inflation_power_increment_bound (R:realType) (v:R) m d:
  1<=v ->(1+m%:R/v)^+d<=
    1+(m%:R*(\sum_(i<d) (1+m%:R)^+i))/v.
Proof.
move=>hv1.
have hv:0<v:=lt_le_trans ltr01 hv1.
have ht0:0<=v^-1 by rewrite invr_ge0; exact:ltW hv.
have ht1:v^-1<=1 by rewrite invf_le1.
have hs0:0<=m%:R/v:=mulr_ge0 (ler0n R m) ht0.
have hsBound:m%:R/v<=m%:R.
  have h:=ler_wpM2l (ler0n R m) ht1; by rewrite mulr1 in h.
have hBound:=nonnegative_power_linear_increment_bound d hs0 hsBound.
have hAlgebra:(m%:R/v)*(\sum_(i<d) (1+(m%:R:R))^+i)=
    (m%:R*(\sum_(i<d) (1+(m%:R:R))^+i))/v by ring.
by rewrite hAlgebra in hBound.
Qed.

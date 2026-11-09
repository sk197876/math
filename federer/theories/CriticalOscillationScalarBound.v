(** Federer (1969), 3.4.2(6), p. 312: scalar bounds for the
    oscillation estimate along the original retracted segment. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm ExtendedSupremumUP RealPower RealPowerSuccessor
  CriticalOscillationUP CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_eta_finite_upper_bound]: the passage from
    bounds on every original increment to an η bound at the end of
    3.4.2(6), p. 312. The adjoined zero requires a nonnegative bound;
    all positive-distance tests remain in the original source family. *)
Theorem critical_eta_finite_upper_bound (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta b:R):
  0<=b ->
  (forall x c,S x ->C c ->Z (x-c) ->
    0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta ->
    NY (f x-f c)<=b*real_power
      (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda) ->
  (critical_eta NY Z S C f lambda delta<=b%:E)%E.
Proof.
move=>hb hBound.
apply:(extended_supremum_least (critical_eta_laws NY Z S C f lambda delta)).
move=>q [->|[x [c [hx [hc [hZ [hDist ->]]]]]]];first by rewrite lee_fin.
rewrite lee_fin (ler_pdivrMr _ _ (@real_power_strictly_positive R _ lambda (andP hDist).1)).
exact:(hBound x c hx hc hZ hDist).
Qed.

(** Source for [critical_power_derivative_factor_bound]: the factor
    M^lambda in the derivative estimate of 3.4.2(6), p. 312. Bounds
    for the curve speed and its distance from c combine with
    lambda>=1, including the endpoint lambda=1. *)
Lemma critical_power_derivative_factor_bound (R:realType) (r s M d b lambda:R):
  0<=r ->0<=s ->0<M ->0<d ->0<=b ->1<=lambda ->
  r<=M*d ->s<=M*d ->
  r*b*real_power s (lambda-1)<=
    real_power M lambda*b*real_power d lambda.
Proof.
move=>hr hs hM hd hb hLambda hrBound hsBound.
have hExponent:0<=lambda-1 by lra.
have hPower:real_power s (lambda-1)<=real_power (M*d) (lambda-1).
  case:(eqVneq (lambda-1) 0)=>[hZero|hNonzero].
  - by rewrite hZero !real_power_zero_exponent.
  - have hPositive:0<lambda-1 by rewrite lt_def hNonzero hExponent.
    exact:(@real_power_monotone R s (M*d) (lambda-1) hs hsBound hPositive).
have hNonnegative:=real_power_nonnegative s (lambda-1).
have hFirst:r*b*real_power s (lambda-1)<=
    (M*d)*b*real_power s (lambda-1).
  exact:(ler_wpM2r hNonnegative (ler_wpM2r hb hrBound)).
have hSecond:(M*d)*b*real_power s (lambda-1)<=
    (M*d)*b*real_power (M*d) (lambda-1).
  have hCoefficient:0<=(M*d)*b:=mulr_ge0 (mulr_ge0 (ltW hM) (ltW hd)) hb.
  exact:(ler_wpM2l hCoefficient hPower).
have hMpow:real_power M lambda=real_power M (lambda-1)*M.
  have hh:=@real_power_add_exponents_positive R M (lambda-1) 1 hM.
  by rewrite subrK (@real_power_one_exponent R M (ltW hM)) in hh.
have hDpow:real_power d lambda=real_power d (lambda-1)*d.
  have hh:=@real_power_add_exponents_positive R d (lambda-1) 1 hd.
  by rewrite subrK (@real_power_one_exponent R d (ltW hd)) in hh.
have hIdentity:(M*d)*b*real_power (M*d) (lambda-1)=
    real_power M lambda*b*real_power d lambda.
  rewrite (@real_power_product R M d (lambda-1) (ltW hM) (ltW hd)) hMpow hDpow;ring.
rewrite hIdentity in hSecond.
exact:(le_trans hFirst hSecond).
Qed.

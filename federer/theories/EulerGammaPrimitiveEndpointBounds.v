(** Federer (1969), 3.2.13, p. 250: vanishing
    endpoint terms for the Gamma recurrence. Bounds
    at zero and infinity are proved from
    the internal exponential and real-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra ring.
From Federer Require Import EulerGammaUP EulerGammaPrimitiveDifferential EulerGammaBounds EulerGammaOriginBounds
  RealPower RealPowerSuccessor RealExponentialSealed RealExponentialUP GeometricUniformTail
  ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_gamma_primitive_integrand]: the
    endpoint product in the Gamma recurrence is
    the defining integrand with parameter s+1,
    Federer 3.2.13, p. 250. *)
Lemma euler_gamma_primitive_integrand (R:realType) (s x:R):
  euler_gamma_primitive s x=euler_gamma_integrand (s+1) x.
Proof. rewrite /euler_gamma_primitive /euler_gamma_integrand addrK; ring. Qed.

(** Source for [euler_gamma_primitive_origin_upper]: the
    endpoint product is at most x^s on
    the positive ray, supporting the recurrence
    in Federer 3.2.13, p. 250. *)
Lemma euler_gamma_primitive_origin_upper (R:realType) (s x:R):
  0<x ->0<=euler_gamma_primitive s x<=real_power x s.
Proof.
move=>hx; apply/andP; split.
- rewrite euler_gamma_primitive_integrand; exact:ltW (euler_gamma_integrand_positive (s+1) hx).
- have hh:=gamma_integrand_exponential_upper (s+1) hx.
  by rewrite addrK -euler_gamma_primitive_integrand in hh.
Qed.

(** Source for [euler_gamma_primitive_origin_dyadic_limit]:
    the origin endpoint x^s exp(-x) tends
    to zero along positive dyadic endpoints for
    s>0, in the recurrence of Federer
    3.2.13, p. 250. *)
Lemma euler_gamma_primitive_origin_dyadic_limit (R:realType) (s:R):
  0<s ->extended_order_limit (fun n=>(euler_gamma_primitive s ((1/2)^+n))%:E) (0%R)%:E.
Proof.
move=>hs.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<1) by lra.
pose q:=real_power (1/2:R) s.
have hq0:0<q:=real_power_strictly_positive s hHalf.
have hq1:q<1.
  have hh:=real_power_strict_monotone (ltW hHalf) hHalf1 hs.
  by rewrite real_power_one_base in hh.
apply:real_error_extended_order_limit=>e he.
have hq:0<q<1 by apply/andP; split.
have hOne:0<=(1:R) by exact:ler01.
have [N hN]:=geometric_uniform_tail hq hOne he.
exists N=>n hn.
have hSmall:=hN n hn; rewrite mulr1 in hSmall.
have /andP[hLow hUp]:=euler_gamma_primitive_origin_upper s (exprn_gt0 n hHalf).
rewrite gamma_power_of_natural_base ?(ltW hHalf) // in hUp.
rewrite subr0 ger0_norm //; exact:le_lt_trans hUp hSmall.
Qed.

(** Source for [euler_gamma_primitive_tail_dyadic_limit]:
    the infinity endpoint x^s exp(-x) tends
    to zero along growing dyadic endpoints, supporting
    the Gamma recurrence in Federer 3.2.13,
    p. 250. No real-power growth comparison is assumed. *)
Lemma euler_gamma_primitive_tail_dyadic_limit (R:realType) (s:R):
  extended_order_limit (fun n=>(euler_gamma_primitive s ((2:R)^+n))%:E) (0%R)%:E.
Proof.
pose k:=Num.truncn (Order.max (s+1) 0).
have hMax:0<=Order.max (s+1) 0 by rewrite le_max lexx orbT.
have /andP[_ hK]:=truncn_itv hMax.
have hs:s+1<=k.+1%:R.
  apply:le_trans _ (ltW hK); by rewrite le_max lexx.
pose C:=((k.+2)%:R:R)^+k.+2.
have hC:0<=C by apply:exprn_ge0; exact:ler0n.
have hTwo:0<(2:R) by lra.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<1) by lra.
have hBound n:0<=euler_gamma_primitive s ((2:R)^+n)<=C*(1/2)^+n.
  have hPos:0<(2:R)^+n:=exprn_gt0 n hTwo.
  have hPowerOne j:1<=(2:R)^+j.
    elim:j=>[|j ih]; first by rewrite expr0.
    rewrite exprS; nra.
  have hh:=euler_gamma_integrand_tail_bound hs (hPowerOne n).
  rewrite -euler_gamma_primitive_integrand in hh.
  have hInv:((2:R)^+n)^-1=(1/2)^+n by rewrite div1r exprVn.
  rewrite hInv in hh.
  have hSmall:0<=(1/2:R)^+n<= 1.
    apply/andP; split; first exact:ltW (exprn_gt0 n hHalf).
    exact (exprn_ile1 n (ltW hHalf) (ltW hHalf1)).
  apply/andP; split.
  - rewrite euler_gamma_primitive_integrand; exact:ltW (euler_gamma_integrand_positive (s+1) hPos).
  - apply:le_trans hh _.
    apply:(ler_wpM2l hC); rewrite expr2; nra.
apply:real_error_extended_order_limit=>e he.
have hq:0<(1/2:R)<1 by apply/andP; split.
have [N hN]:=geometric_uniform_tail hq hC he.
exists N=>n hn; have /andP[hLow hUp]:=hBound n.
rewrite subr0 ger0_norm //; apply:le_lt_trans hUp _.
by rewrite mulrC; exact:hN n hn.
Qed.

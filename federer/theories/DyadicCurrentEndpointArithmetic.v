(** Federer (1969), 4.1.12, p. 368: the
    first interval series has endpoints 2^(-2k)
    and 2^(1-2k), k>=1, and total length 1/3.
    Formal index n denotes the printed k=n+1.
    Use the identical powers (1/4)^(n+1). *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dyadic_current_left_endpoint]: the
    original left endpoint 2^(-2(n+1)), Federer
    4.1.12, p. 368, in its equal
    quarter-power presentation. *)
Definition dyadic_current_left_endpoint (R:realType) n:R:=(1/4)^+n.+1.

(** Source for [dyadic_current_right_endpoint]: the
    original right endpoint 2^(1-2(n+1)), Federer
    4.1.12, p. 368. *)
Definition dyadic_current_right_endpoint (R:realType) n:R:=
  2*dyadic_current_left_endpoint R n.

(** Source for [dyadic_current_mass_tail]: the
    remaining length after n original intervals is
    (1/4)^n/3, supporting the exact mass
    calculation in Federer 4.1.12, p. 368. *)
Definition dyadic_current_mass_tail (R:realType) n:R:=(1/4)^+n/3.

(** Source for [dyadic_current_endpoint_bounds]: every
    original interval is positively oriented inside
    [0,1/2], supporting the compact support in
    Federer 4.1.12, p. 368. *)
Lemma dyadic_current_endpoint_bounds (R:realType) n:
  0<dyadic_current_left_endpoint R n /\
  dyadic_current_left_endpoint R n<dyadic_current_right_endpoint R n /\
  dyadic_current_right_endpoint R n<=1/2.
Proof.
pose q:R:=1/4.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hPower:0<q^+n.+1:=exprn_gt0 n.+1 (andP hq).1.
have hLe:q^+n.+1<=q.
  rewrite exprSr.
  have h:=ler_wpM2r (ltW (andP hq).1)
    (exprn_ile1 n (ltW (andP hq).1) (ltW (andP hq).2)).
  by rewrite mul1r in h.
change (0<q^+n.+1 /\q^+n.+1<2*q^+n.+1 /\2*q^+n.+1<=1/2).
split;first exact:hPower.
split;rewrite /q in hLe;lra.
Qed.

(** Source for [dyadic_current_interval_length]: each
    original interval has length 4^(-(n+1)), supporting
    the mass series in Federer 4.1.12, p. 368. *)
Lemma dyadic_current_interval_length (R:realType) n:
  dyadic_current_right_endpoint R n-dyadic_current_left_endpoint R n=
    dyadic_current_left_endpoint R n.
Proof. rewrite /dyadic_current_right_endpoint;ring. Qed.

(** Source for [dyadic_current_mass_tail_step]: exact
    consecutive tail differences are the original
    interval lengths, supporting Federer 4.1.12, p. 368. *)
Lemma dyadic_current_mass_tail_step (R:realType) n:
  dyadic_current_mass_tail R n-dyadic_current_mass_tail R n.+1=
    dyadic_current_left_endpoint R n.
Proof.
rewrite /dyadic_current_mass_tail /dyadic_current_left_endpoint !exprSr.
field;by rewrite ?pnatr_eq0.
Qed.

(** Source for [dyadic_current_mass_tail_nonnegative]:
    original mass tails are nonnegative, supporting
    the series of Federer 4.1.12, p. 368. *)
Lemma dyadic_current_mass_tail_nonnegative (R:realType) n:
  0<=dyadic_current_mass_tail R n.
Proof.
rewrite /dyadic_current_mass_tail.
have hq:0<=(1/4:R) by lra.
apply:divr_ge0;first exact:(exprn_ge0 n hq).
by rewrite ler0n.
Qed.

(** Source for [dyadic_current_mass_tail_small]: the
    original remaining mass tends to zero, supporting
    convergence in Federer 4.1.12, p. 368. *)
Lemma dyadic_current_mass_tail_small (R:realType) epsilon:
  0<epsilon->exists k,dyadic_current_mass_tail R k<epsilon.
Proof.
move=>hEpsilon.
have hq:0<(1/4:R)<1 by apply/andP;split;lra.
have hM:0<=(1/3:R) by lra.
have[k hk]:=@geometric_uniform_tail R (1/4) (1/3) epsilon hq hM hEpsilon.
exists k;rewrite /dyadic_current_mass_tail !mul1r.
have h:=hk k (leqnn k);by rewrite !mul1r in h.
Qed.

(** Source for [dyadic_current_length_prefix]: the
    first n original lengths sum to 1/3 minus
    the remaining mass tail, supporting the exact
    mass in Federer 4.1.12, p. 368. *)
Lemma dyadic_current_length_prefix (R:realType) n:
  \sum_(k<n) dyadic_current_left_endpoint R k= 1/3-dyadic_current_mass_tail R n.
Proof.
elim:n=>[|n ih].
- by rewrite big_ord0 /dyadic_current_mass_tail expr0 subrr.
- rewrite big_ord_recr /= ih -dyadic_current_mass_tail_step;ring.
Qed.

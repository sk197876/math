(** Federer (1969), 3.2.38, p. 275: inflation of the top
    intrinsic coefficient gives a first-order normalized error. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import GridReversePowerNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grid_steiner_top_term_bound]: supporting the actual
    top-Jacobian term in Federer 3.2.38, p. 275. Its value
    J_m D times cube volume is retained; only the inflation error
    uses a uniform upper bound M. Neither invertibility nor positive
    Jacobian is assumed. Zero normal dimension has no inflation. *)
Lemma grid_steiner_top_term_bound (R:realType) (v r A J M E:R) m n:
  0<v ->0<r ->0<=J ->J<=M ->0<=E ->(m<=n)%N ->
  A^+(n-m)<=1+E/v ->
  (J*(v*r)^+m)*(A*r)^+(n-m)/r^+(n-m)<=
    J*(v*r)^+m+(M*E/v)*(v*r)^+m.
Proof.
move=>hv hr hJ hJM hE hmn hPower.
have hMass:0<=(v*r)^+m:=exprn_ge0 _ (mulr_ge0 (ltW hv) (ltW hr)).
have hShape:(J*(v*r)^+m)*(A*r)^+(n-m)/r^+(n-m)=
    J*((v*r)^+m*(A*r)^+(n-m)/r^+(n-m)) by ring.
rewrite hShape (@grid_reverse_power_normalization R v r A m m n hv hr (leqnn m) hmn)
  subnn expr0 mulr1.
have hFirst:J*((v*r)^+m*A^+(n-m))<=
    J*(v*r)^+m*(1+E/v).
  have h:=ler_wpM2l (mulr_ge0 hJ hMass) hPower.
  by rewrite mulrA.
apply:le_trans hFirst _.
have hErrorNonnegative:0<=(E/v)*(v*r)^+m.
  exact:mulr_ge0 (divr_ge0 hE (ltW hv)) hMass.
have hError:=ler_wpM2r hErrorNonnegative hJM.
have hLeft:J*(v*r)^+m*(1+E/v)=J*(v*r)^+m+J*((E/v)*(v*r)^+m) by ring.
have hRight:J*(v*r)^+m+(M*E/v)*(v*r)^+m=
    J*(v*r)^+m+M*((E/v)*(v*r)^+m) by ring.
rewrite hLeft hRight; exact:lerD (lexx _) hError.
Qed.

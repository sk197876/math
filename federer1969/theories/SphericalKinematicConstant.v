(** Federer (1969), 3.2.48, pp. 284, 286: the
    actual projection-beta ratio and sphere normalization give the
    printed Gamma coefficient. All factors cancelled below are
    positive actual Euler Gamma values; degree zero is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal ring lra.
From Federer Require Import ProjectionBeta ProjectionBetaFirstGamma ProjectionBetaZeroDegree
  GammaHalfSequences EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_first_gamma_all_degrees]: the
    3.2.13, p. 251, Gamma quotient with its literal
    zero-degree boundary, needed in 3.2.48, p. 286.
    Beta_1(n,0)=1 is proved by its independent probability laws. *)
Lemma projection_beta_first_gamma_all_degrees (R:realType) n p (hpn:(p<=n)%N):
  @projection_beta R n p hpn (1:R)%:E=
    gamma_half_sequence R p*gamma_half_sequence R (n-p)/
      (gamma_half_sequence R n*gamma_half_sequence R 0%N).
Proof.
case:p hpn=>[|p] hpn.
- rewrite projection_beta_zero_degree // subn0.
  rewrite [gamma_half_sequence R 0%N*gamma_half_sequence R n]mulrC.
  have hNonzero:gamma_half_sequence R n*gamma_half_sequence R 0%N!=0.
    exact (mulf_neq0 (lt0r_neq0 (gamma_half_sequence_positive R n))
      (lt0r_neq0 (gamma_half_sequence_positive R 0%N))).
  by rewrite divff.
- exact (@projection_beta_first_gamma_formula R n p.+1 (ltn0Sn p) hpn).
Qed.

(** Source for [spherical_kinematic_beta_ratio]: the exact
    isotropy average beta_1(d,d-m)/beta_1(k,d-m),
    evaluated as the printed Gamma ratio in 3.2.48,
    p. 286, by 3.2.13, p. 251. The assumptions
    type the projection constants; no positive-degree requirement is added. *)
Theorem spherical_kinematic_beta_ratio (R:realType) d k m
    (hmd:(m<=d)%N) (hpk:(d-m<=k)%N):
  @projection_beta R d (d-m) (leq_subr m d) (1:R)%:E/
    @projection_beta R k (d-m) hpk (1:R)%:E=
  gamma_half_sequence R k*gamma_half_sequence R m/
    (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)).
Proof.
rewrite !projection_beta_first_gamma_all_degrees.
have hFirst:(d-(d-m)=m)%N by rewrite subKn.
have hSecond:(k-(d-m)=k+m-d)%N.
  by rewrite subnBA // addnC.
rewrite hFirst hSecond.
pose a:=gamma_half_sequence R (d-m).
pose b:=gamma_half_sequence R m.
pose c:=gamma_half_sequence R (k+m-d).
pose e:=gamma_half_sequence R k.
pose f:=gamma_half_sequence R d.
pose z:=gamma_half_sequence R 0%N.
have ha:a!=0 by rewrite gt_eqF //; exact:gamma_half_sequence_positive.
have hz:z!=0 by rewrite gt_eqF //; exact:gamma_half_sequence_positive.
rewrite !invfM !invrK.
have hReorder:(a*b*(f^-1*z^-1))*(a^-1*c^-1*(e*z))=
    (a*a^-1)*(z*z^-1)*(e*b)*(f^-1*c^-1) by ring.
by rewrite hReorder !mulfV // !mul1r.
Qed.

(** Source for [spherical_kinematic_constant]: the coefficient
    Gamma((k+1)/2) Gamma((m+1)/2) divided by
    2 Gamma(1/2)^(d+1) Gamma((k+m-d+1)/2),
    in 3.2.48, p. 284. The half-sequence is the
    actual Euler Gamma evaluation, not a new normalization axiom. *)
Definition spherical_kinematic_constant (R:realType) d k m:R:=
  gamma_half_sequence R k*gamma_half_sequence R m/
    (2*(euler_gamma_half R)^+d.+1*gamma_half_sequence R (k+m-d)).

(** Source for [spherical_kinematic_constant_positive]: strict
    positivity of the actual printed coefficient, supporting
    all cancellations in 3.2.48, p. 286. *)
Lemma spherical_kinematic_constant_positive (R:realType) d k m:
  0<spherical_kinematic_constant R d k m.
Proof.
apply:divr_gt0.
- exact (mulr_gt0 (gamma_half_sequence_positive R k) (gamma_half_sequence_positive R m)).
- apply:mulr_gt0; last exact:gamma_half_sequence_positive.
  apply:mulr_gt0; first by rewrite ltr0n.
  exact (exprn_gt0 _ (euler_gamma_positive _)).
Qed.

(** Source for [spherical_kinematic_constant_normalization]: the
    final scalar cancellation in 3.2.48, p. 286:
    isotropy average divided by sphere area is the printed
    coefficient. The original actual positive Gamma factors are retained. *)
Lemma spherical_kinematic_constant_normalization (R:realType) d k m:
  (gamma_half_sequence R k*gamma_half_sequence R m/
    (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)))/
    (2*(euler_gamma_half R)^+d.+1/gamma_half_sequence R d)=
  spherical_kinematic_constant R d k m.
Proof.
have hd:gamma_half_sequence R d!=0.
  by rewrite gt_eqF //; exact:gamma_half_sequence_positive.
rewrite /spherical_kinematic_constant !invfM !invrK.
have hReorder:(gamma_half_sequence R k*gamma_half_sequence R m*
    ((gamma_half_sequence R d)^-1*(gamma_half_sequence R (k+m-d))^-1))*
    (2^-1*((euler_gamma_half R)^+d.+1)^-1*gamma_half_sequence R d)=
  ((gamma_half_sequence R d)^-1*gamma_half_sequence R d)*
    (gamma_half_sequence R k*gamma_half_sequence R m*
      (2^-1*((euler_gamma_half R)^+d.+1)^-1*(gamma_half_sequence R (k+m-d))^-1)) by ring.
by rewrite hReorder mulVf // mul1r.
Qed.

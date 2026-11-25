(** Federer (1969), 3.4.5, p. 321: finite
    coefficients in the quadratic substitution parameter,
    supporting the actual flat-coefficient obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import ShiftedAffinePowerCoefficients QuadraticSubstitutionKernel QuadraticSubstitutionFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Parameters.
Variable K:fieldType.

(** Source for [quadratic_substitution_parameter_coefficient]: each
    coefficient of the original finite polynomial in lambda
    is a finite linear combination of the original
    divided Taylor coefficients, supporting 3.4.5, p. 321. *)
Definition quadratic_substitution_parameter_coefficient (parity N ell:nat) (a:nat->nat->K):K:=
  \sum_(i<N.+1) \sum_(k<N.+1 | ((ell<=k)&&(i+2*k+parity+ell==N))%N)
    a i k*('C(k,ell))%:R*(-1)^+(k-ell).

(** Source for [quadratic_substitution_parameter_expansion]: the
    original quadratic remainder is an actual finite
    polynomial in its substitution parameter, with every
    original coefficient retained, supporting 3.4.5, p. 321. *)
Theorem quadratic_substitution_parameter_expansion parity (lambda:K) N (a:nat->nat->K):
  quadratic_substitution_weighted_sum parity lambda N a=
    \sum_(ell<N.+1) lambda^+ell*quadratic_substitution_parameter_coefficient parity N ell a.
Proof.
have hLine (i:nat) (k:'I_N.+1):
    a i k*quadratic_substitution_kernel parity lambda N i k=
    \sum_(ell<N.+1 | ((ell<=k)&&(i+2*k+parity+ell==N))%N)
      lambda^+ell*(a i k*('C(k,ell))%:R*(-1)^+(k-ell)).
  rewrite /quadratic_substitution_kernel /shifted_affine_power_coefficient big_mkcond mulr_sumr.
  have hBound:(k.+1<=N.+1)%N:=ltn_ord k.
  rewrite (big_ord_widen N.+1 (fun ell=>a i k*
    (if (i+2*k+parity+ell==N)%N then ('C(k,ell))%:R*(-1)^+(k-ell)*lambda^+ell else 0)) hBound)
    big_mkcond [RHS]big_mkcond.
  apply:eq_bigr=>ell _;rewrite ltnS.
  by case:(ell<=k)%N;case:(i+2*k+parity+ell==N)%N;rewrite /= ?mulr0;ring.
have hRow (i:nat):
    (\sum_(k<N.+1) a i k*quadratic_substitution_kernel parity lambda N i k)=
    \sum_(ell<N.+1) lambda^+ell*
      \sum_(k<N.+1 | ((ell<=k)&&(i+2*k+parity+ell==N))%N)
        a i k*('C(k,ell))%:R*(-1)^+(k-ell).
  under eq_bigr do rewrite hLine big_mkcond.
  rewrite exchange_big;apply:eq_bigr=>ell _.
  by rewrite mulr_sumr [RHS]big_mkcond.
rewrite /quadratic_substitution_weighted_sum.
under eq_bigr do rewrite hRow.
rewrite exchange_big;apply:eq_bigr=>ell _.
by rewrite /quadratic_substitution_parameter_coefficient mulr_sumr.
Qed.
End Parameters.

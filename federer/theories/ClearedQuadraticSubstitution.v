(** Federer (1969), 3.4.5, p. 321: exact
    finite denominator clearing for the quadratic remainder
    in the actual flat-coefficient obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import QuadraticSubstitutionFunctional QuadraticSubstitutionParameterCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Clearing.
Variable K:fieldType.

(** Source for [finite_cleared_power_product]: the original
    parameter substitution c/z has a finite polynomial
    numerator at every coefficient order, supporting
    3.4.5, p. 321. Only the actual nonzero
    denominator and original finite order bound are used. *)
Lemma finite_cleared_power_product (z c a:K) (N ell:nat):
  z!=0 ->(ell<=N)%N ->
  z^+N*(a*(c/z)^+ell)=a*z^+(N-ell)*c^+ell.
Proof.
move=>hz hEll.
have hZPower:z^+ell!=0 by apply:expf_neq0.
have hCancel:z^+ell*(c^+ell/z^+ell)=c^+ell by rewrite mulrC divfK.
have hSplit:N=(N-ell+ell)%N by rewrite subnK.
rewrite {1}hSplit exprD expr_div_n.
transitivity (a*(z^+(N-ell)*(z^+ell*(c^+ell/z^+ell))));first ring.
by rewrite hCancel mulrA.
Qed.

(** Source for [quadratic_cleared_remainder]: the exact
    finite original quadratic remainder after clearing powers
    of z, supporting 3.4.5, p. 321. Its
    coefficients involve no division, including at z=0. *)
Definition quadratic_cleared_remainder (parity N:nat) (z c:K) (a:nat->nat->K):K:=
  \sum_(ell<N.+1) z^+(N-ell)*c^+ell*quadratic_substitution_parameter_coefficient parity N ell a.

(** Source for [quadratic_cleared_remainder_value]: at every
    original nonzero z the cleared polynomial is exactly
    z^N times the original substituted remainder, supporting
    the actual coefficient argument in 3.4.5, p. 321. *)
Theorem quadratic_cleared_remainder_value parity N (z c:K) (a:nat->nat->K):
  z!=0 ->quadratic_cleared_remainder parity N z c a=
    z^+N*quadratic_substitution_weighted_sum parity (c/z) N a.
Proof.
move=>hz;rewrite /quadratic_cleared_remainder quadratic_substitution_parameter_expansion mulr_sumr.
apply:eq_bigr=>ell _.
have hEll:(ell<=N)%N by have:=ltn_ord ell;rewrite ltnS.
pose A:=quadratic_substitution_parameter_coefficient parity N ell a.
have hPower:=@finite_cleared_power_product z c A N ell hz hEll.
change (z^+(N-ell)*c^+ell*A=z^+N*((c/z)^+ell*A)).
transitivity (A*z^+(N-ell)*c^+ell);first ring.
rewrite -hPower;ring.
Qed.

(** Source for [quadratic_cleared_remainder_multiple]: the
    original finite cleared remainder of an actual coefficient
    multiple of z*(x^2+y^2)-c*x^3 is zero at every
    nonzero z, supporting 3.4.5, p. 321.
    The substitution relation and every cancellation are proved. *)
Theorem quadratic_cleared_remainder_multiple (h0:[pchar K]=i pred0) parity N (z c:K)
    (a:nat->nat->K):
  z!=0 ->quadratic_cleared_remainder parity N z c
    (fun i k=>z*(if (2<=i)%N then a (i-2)%N k else 0)+
      z*(if (1<=k)%N then a i (k-1)%N else 0)-
      c*(if (3<=i)%N then a (i-3)%N k else 0))=0.
Proof.
move=>hz.
have hRelation:z*(c/z)=c by rewrite mulrC divfK.
rewrite quadratic_cleared_remainder_value //
  (@quadratic_substitution_annihilates_multiple K h0 parity (c/z) N a z c hRelation) mulr0.
by [].
Qed.
End Clearing.

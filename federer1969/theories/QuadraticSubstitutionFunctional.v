(** Federer (1969), 3.4.5, p. 321: finite
    quadratic-substitution coefficient functionals and the exact
    cancellation for multiples of the original equation. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import QuadraticSubstitutionKernel FinitePaddedShiftSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Functional.
Variable K:fieldType.

(** Source for [quadratic_substitution_weighted_sum]: the
    exact finite coefficient at order N after the original
    parity substitution, supporting 3.4.5, p. 321.
    The supplied array has already separated its y parity. *)
Definition quadratic_substitution_weighted_sum parity (lambda:K) N (a:nat->nat->K):K:=
  \sum_(i<N.+1) \sum_(k<N.+1) a i k*quadratic_substitution_kernel parity lambda N i k.

(** Source for [quadratic_substitution_weighted_three_terms]: finite
    linearity of the original remainder coefficient functional,
    supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_weighted_three_terms parity lambda N (a b c:nat->nat->K) z t:
  quadratic_substitution_weighted_sum parity lambda N (fun i k=>z*a i k+z*b i k-t*c i k)=
    z*quadratic_substitution_weighted_sum parity lambda N a+
    z*quadratic_substitution_weighted_sum parity lambda N b-
    t*quadratic_substitution_weighted_sum parity lambda N c.
Proof.
rewrite /quadratic_substitution_weighted_sum.
have hLine (i:nat):
    (\sum_(k<N.+1) (z*a i k+z*b i k-t*c i k)*quadratic_substitution_kernel parity lambda N i k)=
    z*(\sum_(k<N.+1) a i k*quadratic_substitution_kernel parity lambda N i k)+
    z*(\sum_(k<N.+1) b i k*quadratic_substitution_kernel parity lambda N i k)-
    t*(\sum_(k<N.+1) c i k*quadratic_substitution_kernel parity lambda N i k).
  under eq_bigr do rewrite mulrBl mulrDl -!mulrA.
  by rewrite sumrB big_split -!mulr_sumr.
under eq_bigr do rewrite hLine.
by rewrite sumrB big_split -!mulr_sumr.
Qed.

(** Source for [quadratic_substitution_weighted_first_shift]: an
    original finite x coefficient shift transfers to the
    actual kernel, supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_weighted_first_shift parity lambda N (a:nat->nat->K) d:
  quadratic_substitution_weighted_sum parity lambda N
    (fun i k=>if (d<=i)%N then a (i-d)%N k else 0)=
    \sum_(i<N.+1) \sum_(k<N.+1) a i k*quadratic_substitution_kernel parity lambda N (i+d)%N k.
Proof.
rewrite /quadratic_substitution_weighted_sum exchange_big.
have hLine (k:nat):
    (\sum_(i<N.+1) (if (d<=i)%N then a (i-d)%N k else 0)*quadratic_substitution_kernel parity lambda N i k)=
    \sum_(i<N.+1) a i k*quadratic_substitution_kernel parity lambda N (i+d)%N k.
  apply:(@finite_padded_shift_sum K N.+1 d (fun i=>a i k)
    (fun i=>quadratic_substitution_kernel parity lambda N i k))=>i hi.
  exact:(@quadratic_substitution_kernel_first_cutoff K parity lambda N i k hi).
under eq_bigr do rewrite hLine.
exact:exchange_big.
Qed.

(** Source for [quadratic_substitution_weighted_second_shift]: the
    paired original y coefficient shift transfers to the
    actual kernel, supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_weighted_second_shift parity lambda N (a:nat->nat->K) d:
  quadratic_substitution_weighted_sum parity lambda N
    (fun i k=>if (d<=k)%N then a i (k-d)%N else 0)=
    \sum_(i<N.+1) \sum_(k<N.+1) a i k*quadratic_substitution_kernel parity lambda N i (k+d)%N.
Proof.
rewrite /quadratic_substitution_weighted_sum.
apply:eq_bigr=>i _.
apply:(@finite_padded_shift_sum K N.+1 d (a i)
  (fun k=>quadratic_substitution_kernel parity lambda N i k))=>k hk.
exact:(@quadratic_substitution_kernel_second_cutoff K parity lambda N i k hk).
Qed.

(** Source for [quadratic_substitution_annihilates_multiple]: the
    actual finite remainder of every original coefficient
    multiple of z*(x^2+y^2)-c*x^3 vanishes whenever the
    substitution parameter satisfies z*lambda=c, supporting
    3.4.5, p. 321. The finite kernel recurrence
    and exact padding laws prove the cancellation. *)
Theorem quadratic_substitution_annihilates_multiple (h0:[pchar K]=i pred0) parity lambda N
    (a:nat->nat->K) (z c:K):
  z*lambda=c ->
  quadratic_substitution_weighted_sum parity lambda N
    (fun i k=>z*(if (2<=i)%N then a (i-2)%N k else 0)+
      z*(if (1<=k)%N then a i (k-1)%N else 0)-
      c*(if (3<=i)%N then a (i-3)%N k else 0))=0.
Proof.
move=>hCoefficient.
rewrite quadratic_substitution_weighted_three_terms
  quadratic_substitution_weighted_first_shift quadratic_substitution_weighted_second_shift
  quadratic_substitution_weighted_first_shift.
rewrite !mulr_sumr -big_split -sumrB.
apply:big1=>i _.
rewrite !mulr_sumr -big_split -sumrB.
apply:big1=>k _.
change (z*(a i k*quadratic_substitution_kernel parity lambda N (i+2)%N k)+
  z*(a i k*quadratic_substitution_kernel parity lambda N i (k+1)%N)-
  c*(a i k*quadratic_substitution_kernel parity lambda N (i+3)%N k)=0).
rewrite addn1 (@quadratic_substitution_kernel_successor K h0 parity lambda N i k) -hCoefficient.
ring.
Qed.
End Functional.

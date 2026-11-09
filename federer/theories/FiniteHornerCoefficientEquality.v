(** Federer (1969), 3.4.5, p. 321: finite
    coefficient comparisons in the real cubic-cone Taylor
    argument. The proofs use the internal root-count
    theorem of 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PolynomialCoefficientUniqueness ScalarPolynomialCoefficientCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_power_coefficients_equal]: actual
    finite power sums have unique coefficients, supporting
    the cubic-cone argument in 3.4.5, p. 321. *)
Lemma finite_power_coefficients_equal (K:fieldType) (h0:[pchar K]=i pred0)
    (V:lmodType K) N (a b:nat->V):
  (forall t:K,\sum_(i<N) t^+i*:a i=\sum_(i<N) t^+i*:b i) ->
  forall i,(i<N)%N ->a i=b i.
Proof.
move=>hValues i hi.
have hZero t:(\sum_(i<N) t^+i*:(a i-b i))=0.
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB hValues subrr.
have hEqual:=@finite_power_coefficients_zero K h0 V N (fun i=>a i-b i) hZero i hi.
by move/eqP:hEqual;rewrite subr_eq0=>/eqP.
Qed.

(** Source for [finite_horner_padded_sum]: zero padding
    preserves every original Horner polynomial value,
    supporting finite coefficient comparison in 3.4.5, p. 321. *)
Lemma finite_horner_padded_sum (K:fieldType) (V:lmodType K) (s:seq V) N (t:K):
  (size s<=N)%N ->coefficient_polynomial_value s t=\sum_(i<N) t^+i*:nth 0 s i.
Proof.
move=>hN;rewrite coefficient_polynomial_sum
  (big_ord_widen N (fun i=>t^+i*:nth 0 s i) hN) big_mkcond.
apply:eq_bigr=>i _;case hi:(i<size s)%N;first by [].
have hSize:(size s<=i)%N by rewrite leqNgt hi.
by rewrite (nth_default _ hSize) scaler0.
Qed.

(** Source for [finite_horner_coefficients_equal]: equality
    of original Horner values determines every coefficient,
    including zero padding, supporting 3.4.5, p. 321. *)
Theorem finite_horner_coefficients_equal (K:fieldType) (h0:[pchar K]=i pred0)
    (V:lmodType K) (s r:seq V):
  (forall t:K,coefficient_polynomial_value s t=coefficient_polynomial_value r t) ->
  forall i,nth 0 s i=nth 0 r i.
Proof.
move=>hValues.
pose N:=maxn (size s) (size r).
have hS:(size s<=N)%N:=leq_maxl _ _.
have hR:(size r<=N)%N:=leq_maxr _ _.
have hPowers t:(\sum_(i<N) t^+i*:nth 0 s i)=\sum_(i<N) t^+i*:nth 0 r i.
  by rewrite -(finite_horner_padded_sum t hS) -(finite_horner_padded_sum t hR) hValues.
move=>i;case:(ltnP i N)=>[hi|hi].
- exact:(@finite_power_coefficients_equal K h0 V N (fun i=>nth 0 s i) (fun i=>nth 0 r i) hPowers i hi).
- by rewrite !nth_default //;[exact:leq_trans hR hi|exact:leq_trans hS hi].
Qed.

(** Source for [finite_monomial_shift_coefficient]: the
    coefficient at degree d in an actual shifted
    polynomial determines its monomial coefficient, supporting
    extraction of homogeneous factors in 3.4.5, p. 321. *)
Theorem finite_monomial_shift_coefficient (R:realType) d k (c:R) (b:seq R):
  (forall t:R,t^+d*c=t^+k*@coefficient_polynomial_value R R^o b t) ->
  c=if (d<k)%N then 0 else nth 0 b (d-k)%N.
Proof.
move=>hValues.
pose s:=nseq d 0++[::c].
pose r:=nseq k 0++b.
have hPolynomials t:@coefficient_polynomial_value R R^o s t=
    @coefficient_polynomial_value R R^o r t.
  rewrite /s /r !scalar_polynomial_coefficient_shift_value.
  change (t^+d*(c+t*0)=t^+k*@coefficient_polynomial_value R R^o b t).
  by rewrite mulr0 addr0 hValues.
have hCoefficient:=@finite_horner_coefficients_equal R (@Num.Theory.pchar_num R) R^o s r hPolynomials d.
rewrite /s /r !nth_cat !size_nseq ltnn subnn /= in hCoefficient.
case hLess:(d<k)%N;rewrite hLess in hCoefficient *;last exact:hCoefficient.
by rewrite nth_nseq if_same in hCoefficient.
Qed.

(** Federer (1969), 3.4.5, p. 321: the internal
    finite monic division preserves any specified coefficient
    subring, supporting the actual polynomial counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import FiniteMonicPolynomialDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_monic_polynomial_division_closed]:
    the actual finite quotient and remainder retain polynomial
    coefficient functions, supporting the cubic-cone argument
    in 3.4.5, p. 321. The closure laws concern
    only ordinary coefficient ring operations. *)
Theorem finite_monic_polynomial_division_closed (K:comPzRingType)
    (P:K->Prop) k (d:nat->K) (s:seq K):
  P 0 ->
  (forall a b,P a ->P b ->P (a-b)) ->
  (forall a b,P a ->P b ->P (a*b)) ->
  (forall i,P (d i)) ->
  (forall c,c \in s ->P c) ->
  (0<k)%N ->exists (q:seq K) (r:nat->K),
    (forall c,c \in q ->P c) /\(forall i,P (r i)) /\forall x:K,
    finite_ring_polynomial_value s x=
      finite_ring_polynomial_value q x*(x^+k+\sum_(i<k) d i*x^+i)+
      \sum_(i<k) r i*x^+i.
Proof.
move=>hZero hSubtract hMultiply hDivisor.
case:k=>[|k] hCoefficients hPositive;first by [].
elim:s hCoefficients=>[|c s ih] hCoefficients.
- exists [::],(fun _=>0);split;first by move=>a;rewrite in_nil.
  split;first by move=>i.
  move=>x;rewrite /finite_ring_polynomial_value /= mul0r.
  by rewrite big1 ?addr0 // =>i _;rewrite mul0r.
- have hTail:forall a,a \in s ->P a.
    move=>a ha;apply:hCoefficients;by rewrite in_cons ha orbT.
  have [q [r [hQ [hR hDivision]]]]:=ih hTail.
  pose lead:=r k.
  pose rNew:=fun i:nat=>(if (i==0)%N then c else r (i-1)%N)-lead*d i.
  exists (lead::q),rNew;split.
  + move=>a;rewrite in_cons=>/orP [/eqP ->|ha];[exact:hR|exact:hQ a ha].
  + split.
    * move=>i;apply:hSubtract;last exact:hMultiply (hR k) (hDivisor i).
      case:(i==0)%N;last exact:hR.
      exact:hCoefficients c (mem_head _ _).
    * move=>x.
  have hRemainder:(\sum_(i<k.+1) rNew i*x^+i)=
      c+x*\sum_(i<k) r i*x^+i-lead*\sum_(i<k.+1) d i*x^+i.
    rewrite /rNew.
    under eq_bigr do rewrite mulrBl.
    rewrite sumrB finite_polynomial_shift_remainder.
    congr (_-_);rewrite mulr_sumr;apply:eq_bigr=>i _;ring.
  have hOriginal:(\sum_(i<k.+1) r i*x^+i)=
      (\sum_(i<k) r i*x^+i)+lead*x^+k.
    by rewrite big_ord_recr.
  change (c+x*finite_ring_polynomial_value s x=
    (lead+x*finite_ring_polynomial_value q x)*(x^+k.+1+\sum_(i<k.+1) d i*x^+i)+
    \sum_(i<k.+1) rNew i*x^+i).
  rewrite hDivision hOriginal hRemainder exprS;ring.
Qed.

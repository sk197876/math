(** Federer (1969), 3.4.5, p. 321: internal
    finite monic division supporting the polynomial argument
    for the cited analytic counterexample. The coefficient
    ring may itself consist of polynomial functions. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_ring_polynomial_value]: finite
    Horner evaluation over an arbitrary commutative ring,
    supporting the example cited in 3.4.5, p. 321.
    This extends the field-coefficient support in 1.10.4. *)
Definition finite_ring_polynomial_value (K:comPzRingType) (s:seq K) (x:K):K:=
  foldr (fun c y=>c+x*y) 0 s.

(** Source for [finite_polynomial_shift_remainder]: the
    exact constant-and-shift identity in finite monic division,
    supporting 3.4.5, p. 321. *)
Lemma finite_polynomial_shift_remainder (K:comPzRingType) k (r:nat->K) (c x:K):
  \sum_(i<k.+1) (if ((i:nat)==0)%N then c else r (i-1)%N)*x^+i=
    c+x*\sum_(i<k) r i*x^+i.
Proof.
rewrite big_ord_recl /= expr0 mulr1 mulr_sumr.
congr (c+_);apply:eq_bigr=>i _.
rewrite /= subn1 /= exprS;ring.
Qed.

(** Source for [finite_monic_polynomial_division]: actual
    finite polynomial division by a monic polynomial, supporting
    the cubic-cone elimination in 3.4.5, p. 321.
    The quotient and remainder are proved to exist; no
    division or desired vanishing identity is assumed. *)
Theorem finite_monic_polynomial_division (K:comPzRingType) k (d:nat->K) (s:seq K):
  (0<k)%N ->exists (q:seq K) (r:nat->K),forall x:K,
    finite_ring_polynomial_value s x=
      finite_ring_polynomial_value q x*(x^+k+\sum_(i<k) d i*x^+i)+
      \sum_(i<k) r i*x^+i.
Proof.
case:k=>[//|k] _.
elim:s=>[|c s [q [r hDivision]]].
- exists [::],(fun _=>0)=>x.
  rewrite /finite_ring_polynomial_value /= mul0r.
  by rewrite big1 ?addr0 // =>i _;rewrite mul0r.
- pose lead:=r k.
  pose rNew:=fun i:nat=>(if ((i:nat)==0)%N then c else r (i-1)%N)-lead*d i.
  exists (lead::q),rNew=>x.
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

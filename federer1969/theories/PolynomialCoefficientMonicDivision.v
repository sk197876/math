(** Federer (1969), 3.4.5, p. 321: finite
    monic division with actual polynomial coefficient functions,
    supporting the cubic-cone proof of the cited counterexample.
    Polynomiality is the original symmetric-form predicate of 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricFormSum SymmetricPolynomialEvaluation PolynomialFunctions PolynomialComposition ScalarCoefficients
  FiniteMonicPolynomialDivision FiniteMonicPolynomialDivisionClosed ScalarFunctionRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_ring_polynomial_pointwise]: actual
    evaluation of a polynomial with function coefficients,
    supporting finite division in 3.4.5, p. 321. *)
Lemma finite_ring_polynomial_pointwise (K:comPzRingType) (X:Type)
    (s:seq (X->K)) (t:K) (v:X):
  @finite_ring_polynomial_value (scalar_function_ring_type X K) s (fun _=>t) v=
    finite_ring_polynomial_value [seq a v |a<-s] t.
Proof.
elim:s=>[|a s ih];first by [].
change (a v+t*(@finite_ring_polynomial_value (scalar_function_ring_type X K) s (fun _=>t) v)=
  a v+t*finite_ring_polynomial_value [seq b v |b<-s] t).
by rewrite ih.
Qed.

(** Source for [finite_polynomial_coefficient_monic_division]:
    the actual quotient and remainder still have polynomial
    coefficient functions, supporting the cubic-cone argument
    of 3.4.5, p. 321. The specified divisor
    retains every original coefficient and degree. *)
Theorem finite_polynomial_coefficient_monic_division (R:realType) (X:lmodType R)
    k (d:nat->X->R) (s:seq (X->R)):
  (0<k)%N ->
  (forall i,@is_polynomial_function R X R^o (d i)) ->
  (forall c,c \in s ->@is_polynomial_function R X R^o c) ->
  exists (q:seq (X->R)) (r:nat->X->R),
    (forall c,c \in q ->@is_polynomial_function R X R^o c) /\
    (forall i,@is_polynomial_function R X R^o (r i)) /\
    forall (v:X) (t:R),
      finite_ring_polynomial_value [seq a v |a<-s] t=
      finite_ring_polynomial_value [seq a v |a<-q] t*(t^+k+\sum_(i<k) d i v*t^+i)+
      \sum_(i<k) r i v*t^+i.
Proof.
move=>hK hD hS.
pose K:=(scalar_function_ring_type X R).
pose P:=fun f:K=>@is_polynomial_function R X R^o f.
have hZero:P 0:=@composition_polynomial_constant R X R^o 0.
have hSubtract (f g:K):P f ->P g ->P (f-g).
  move=>[F hF] [G hG];exists ((-1)*:G+F)=>x.
  have h:=congr1 (fun H:X->R=>H x)
    (@symmetric_polynomial_value_linear R X R^o (-1) G F).
  rewrite h.
  change (f x-g x= (-1)*symmetric_polynomial_value G x+symmetric_polynomial_value F x).
  by rewrite mulN1r -hF -hG addrC.
have hMultiply (f g:K):P f ->P g ->P (f*g).
  exact:(@composition_polynomial_product R (@pchar_num R) X R^o
    (fun a b:R^o=>a*b) (@scalar_bilinear R) f g).
have [q [r [hQ [hR hDivision]]]]:=@finite_monic_polynomial_division_closed K P k d s
  hZero hSubtract hMultiply hD hS hK.
exists q,r;split;first exact:hQ.
split;first exact:hR.
move=>v t.
pose T:K:=fun _=>t.
have hPoint:=congr1 (fun f:K=>f v) (hDivision T).
have hEval (l:seq K):@finite_ring_polynomial_value K l T v=
    finite_ring_polynomial_value [seq a v |a<-l] t.
  exact:(@finite_ring_polynomial_pointwise R X l t v).
have hPower j:(T^+j) v=t^+j.
  elim:j=>[|j ih];first by [].
  rewrite !exprS.
  change (t*(T^+j) v=t*t^+j);by rewrite ih.
have hSum (a:nat->K):(\sum_(i<k) a i) v=\sum_(i<k) a i v.
  by elim/big_rec2:_=>[|i y F _ <-].
have hSumPower (a:nat->K):(\sum_(i<k) a i*T^+i) v=\sum_(i<k) a i v*t^+i.
  elim/big_rec2:_=>[|i y F _ <-];first by [].
  change (a i v*(T^+i) v+F v=a i v*t^+i+F v);by rewrite hPower.
change (@finite_ring_polynomial_value K s T v=
  (@finite_ring_polynomial_value K q T v)*
    ((T^+k) v+(\sum_(i<k) (d i:K)*T^+i) v)+
    (\sum_(i<k) r i*T^+i) v) in hPoint.
rewrite !hEval hPower !hSumPower in hPoint.
exact:hPoint.
Qed.

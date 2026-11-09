(** Federer (1969), 3.4.5, p. 321: original
    scalar polynomial coefficients in the internal cubic-cone
    argument are closed under their actual ring operations.
    The proofs use the symmetric-form representation of 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricFormSum SymmetricPolynomialEvaluation
  PolynomialFunctions PolynomialComposition ScalarCoefficients FiniteMonicPolynomialDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarPolynomials.
Variable R:realType.
Variable X:lmodType R.
Local Notation P f:=(@is_polynomial_function R X R^o f).

(** Source for [real_polynomial_add]: actual polynomial
    sums in finite coefficient elimination, supporting
    the example cited in 3.4.5, p. 321. *)
Lemma real_polynomial_add (f g:X->R):P f ->P g ->P (fun x=>f x+g x).
Proof.
move=>[F hF] [G hG];exists (F+G)=>x.
have h:=congr1 (fun H:X->R=>H x)
  (@symmetric_polynomial_value_linear R X R^o 1 F G).
rewrite scale1r in h;rewrite h.
change (f x+g x= 1*symmetric_polynomial_value F x+symmetric_polynomial_value G x).
by rewrite mul1r -hF -hG.
Qed.

(** Source for [real_polynomial_subtract]: actual polynomial
    differences in finite monic division, supporting
    the example cited in 3.4.5, p. 321. *)
Lemma real_polynomial_subtract (f g:X->R):P f ->P g ->P (fun x=>f x-g x).
Proof.
move=>[F hF] [G hG];exists ((-1)*:G+F)=>x.
have h:=congr1 (fun H:X->R=>H x)
  (@symmetric_polynomial_value_linear R X R^o (-1) G F).
rewrite h.
change (f x-g x=(-1)*symmetric_polynomial_value G x+symmetric_polynomial_value F x).
by rewrite mulN1r -hF -hG addrC.
Qed.

(** Source for [real_polynomial_multiply]: actual polynomial
    products in the cubic division argument, supporting
    the example cited in 3.4.5, p. 321. *)
Lemma real_polynomial_multiply (f g:X->R):P f ->P g ->P (fun x=>f x*g x).
Proof.
exact:(@composition_polynomial_product R (@pchar_num R) X R^o
  (fun a b:R^o=>a*b) (@scalar_bilinear R) f g).
Qed.

(** Source for [real_polynomial_power]: actual natural
    powers preserve polynomiality, supporting the cubic
    coefficients in 3.4.5, p. 321. *)
Lemma real_polynomial_power (f:X->R) q:P f ->P (fun x=>(f x)^+q).
Proof.
move=>hf;elim:q=>[|q ih].
- have [F hF]:=@composition_polynomial_constant R X R^o 1.
  exists F=>x;rewrite expr0;exact:hF x.
- have [F hF]:=real_polynomial_multiply hf ih.
  exists F=>x;rewrite exprS;exact:hF x.
Qed.

(** Source for [real_polynomial_coefficient_horner]: finite
    Horner evaluation with original polynomial coefficient
    functions remains polynomial, supporting the actual
    quotient in 3.4.5, p. 321. *)
Lemma real_polynomial_coefficient_horner (h:X->R) (s:seq (X->R)):
  P h ->(forall a,a \in s ->P a) ->
  P (fun x=>finite_ring_polynomial_value [seq a x |a<-s] (h x)).
Proof.
move=>hh;elim:s=>[|c s ih] hCoefficients.
- exact:(@composition_polynomial_constant R X R^o 0).
- have hTail:forall a,a \in s ->P a.
    move=>a ha;apply:hCoefficients;by rewrite in_cons ha orbT.
  change (P (fun x=>c x+h x*finite_ring_polynomial_value [seq a x |a<-s] (h x))).
  exact:(real_polynomial_add (hCoefficients c (mem_head _ _))
    (real_polynomial_multiply hh (ih hTail))).
Qed.
End ScalarPolynomials.

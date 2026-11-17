(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the polynomial algebra of an
    original algebraic element is already a subfield.
    Reuse the proved evaluation-image generation and
    polynomial inverse-value results. Source: Bourbaki,
    Algebra II (1990), Chapter V, section 3,
    no. 1, Theorem 1(c), p. V.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativeSubringUP CommutativeSubfieldUP PolynomialEvaluationImage MinimalPolynomialBezout.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [algebraic_polynomial_image_subfield]: the
    original algebra K[x] is a field for an
    algebraic x in a field, the cited
    Theorem 1(c), p. V.16, supporting
    ring generation in 3.4.8(8), pp. 329–330.
    No inverse membership is added as a premise. *)
Theorem algebraic_polynomial_image_subfield (K:fieldType) (B:comNzRingType) (L:fieldType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}) (x:L) (E:{rmorphism B->L}):
  is_commutative_polynomial_evaluation embed variable phi x E ->
  (exists H:B,H<>0 /\E H = 0) ->
  is_commutative_subfield (fun y:L=>exists P:B,y = E P).
Proof.
move=>hE hAlgebraic.
have hGenerated:=@polynomial_evaluation_image_generated K B L embed variable coefficient hP phi x E hE.
have hRing:=generated_commutative_subring_laws hGenerated.
constructor;first exact:hRing.
move=>y [P ->];case:(eqVneq (E P) 0)=>[hZero|hNonzero].
- rewrite hZero invr0;exact:commutative_subring_zero hRing.
- have hPNonzero:E P<>0 by apply/eqP;exact:hNonzero.
  have [Q hInverse]:=@algebraic_polynomial_image_inverse K B L embed variable coefficient hP E hAlgebraic P hPNonzero.
  exists Q;exact:esym hInverse.
Qed.

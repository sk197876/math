(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: finitely many original polynomial images
    have one common coefficient cutoff. The generator
    list may be empty. Source: the finite-generator
    argument in Artin–Rees, Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3, no. 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets functions.
From Federer Require Import CommutativePolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_polynomial_image_common_support]:
    a finite original generator list has a proved
    common coefficient bound, supporting the cited argument. *)
Lemma finite_polynomial_image_common_support (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (inclusion:{rmorphism C->B}) (F:seq C):
  exists N,forall (i:'I_(size F)) k,(N<=k)%N ->coefficient (inclusion (nth 0 F i)) k = 0.
Proof.
have hEach c:exists N,forall k,(N<=k)%N ->coefficient (inclusion c) k = 0.
  exact:(@polynomial_coefficients_finite A B embed variable coefficient hP (inclusion c)).
have [support hSupport]:=choice hEach.
exists (\max_(i:'I_(size F)) support (nth (0%R:C) F i))=>i k hBound.
apply:hSupport.
exact:(leq_trans (leq_bigmax i) hBound).
Qed.

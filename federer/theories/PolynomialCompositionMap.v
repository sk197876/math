(** Federer (1969), 3.1.11, p. 222: composition of the jet
    polynomials, using the polynomial specification from 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import PolynomialFunctions PolynomialComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polynomial_composite]: Q composed with P,
    the polynomial occurring in the displayed composition-of-jets
    limit, Federer 3.1.11, p. 222. Polynomiality is proved above. *)
Definition polynomial_composite (K : fieldType) (h0 : [pchar K]=i pred0)
    (X Y Z : lmodType K) (P : PolynomialFunction X Y)
    (Q : PolynomialFunction Y Z) : PolynomialFunction X Z :=
  @PolynomialMap K X Z (fun x=>Q (P x))
    (introT (asboolP _) (polynomial_function_composition h0
      (elimT (asboolP _) (polynomial_function_proof P))
      (elimT (asboolP _) (polynomial_function_proof Q)))).

(** Source for [polynomial_compositeE]: pointwise evaluation of
    the composed polynomial in Federer 3.1.11, p. 222. *)
Lemma polynomial_compositeE (K : fieldType) (h0 : [pchar K]=i pred0)
    (X Y Z : lmodType K) (P : PolynomialFunction X Y)
    (Q : PolynomialFunction Y Z) x : polynomial_composite h0 P Q x=Q (P x).
Proof. by []. Qed.

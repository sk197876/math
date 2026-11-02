(** Federer (1969), 1.10.5, p. 47, induced-inner-product monomial
    calculation. Supporting reduction to a finite coordinate space; the
    ambient target need not have finite dimension. This is the biorthogonal
    pairing calculation used for orthonormal families, not an assertion that
    the family spans the ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Hom BoundedHom LinearBasis
  SymmetricAlgebra SymmetricMaps SymmetricLowPowers SymmetricMultiIndices
  SymmetricMonomials SymmetricDividedMonomials SymmetricForms SymmetricFormDual
  SymmetricPairing SymmetricMonomialCoordinates SymmetricDualMonomialProducts
  SymmetricMonomialNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_monomial_pairing_transport]: Federer 1.10.5,
    p. 47, supporting monomial calculation in the proof of positivity.
    If the pulled-back one-forms are dual to a finite basis e, their
    actual products pair with the divided monomials in f(e) by the
    Kronecker rule. No spanning hypothesis on f(e) in the ambient space
    is required. This follows from the dual basis formula of 1.10.2. *)
Theorem symmetric_monomial_pairing_transport (K : fieldType)
    (h0 : [pchar K] =i pred0) (U V : lmodType K) n
    (e : 'I_n -> U) (he : is_basis e) (f : {linear U -> V})
    (omega : 'I_n -> S_m V K^o 1)
    (hd : forall i j, symmetric_pairing (symmetric_first_inclusion U (e j))
      (S_m_dual f (omega i)) = if j == i then 1 else 0)
    (a b : symmetric_multi_index n) :
  symmetric_one_form_monomial omega a (symmetric_divided_monomial (f \o e) b) =
    if b == a then 1 else 0.
Proof.
rewrite -symmetric_divided_monomial_natural -S_star_dualE
  symmetric_one_form_monomial_natural.
rewrite (@symmetric_one_form_monomial_coordinate K U n
  (fun i => S_m_dual f (omega i)) e he h0 hd a).
exact: (@symmetric_coordinate_divided_monomial K U n e he h0 a b).
Qed.

(** Source for [symmetric_ordinary_monomial_pairing_transport]: Federer
    1.10.5, p. 47, supporting Gram-matrix calculation before
    square-root normalization. Multiplying the divided monomial pairing
    by beta! gives the ordinary monomial pairing. *)
Theorem symmetric_ordinary_monomial_pairing_transport (K : fieldType)
    (h0 : [pchar K] =i pred0) (U V : lmodType K) n
    (e : 'I_n -> U) (he : is_basis e) (f : {linear U -> V})
    (omega : 'I_n -> S_m V K^o 1)
    (hd : forall i j, symmetric_pairing (symmetric_first_inclusion U (e j))
      (S_m_dual f (omega i)) = if j == i then 1 else 0)
    (a b : symmetric_multi_index n) :
  symmetric_one_form_monomial omega a (symmetric_monomial (f \o e) b) =
    (symmetric_multi_factorial b)%:R * (if b == a then 1 else 0).
Proof.
have hn := @symmetric_multi_factorial_nonzero K h0 n b.
have hr : symmetric_monomial (f \o e) b =
  ((symmetric_multi_factorial b)%:R : K) *: symmetric_divided_monomial (f \o e) b.
  by rewrite /symmetric_divided_monomial scalerA (mulfV hn) scale1r.
rewrite hr linearZ.
change ((symmetric_multi_factorial b)%:R *
  symmetric_one_form_monomial omega a (symmetric_divided_monomial (f \o e) b) =
  (symmetric_multi_factorial b)%:R * (if b == a then 1 else 0)).
by rewrite (@symmetric_monomial_pairing_transport K h0 U V n e he f omega hd a b).
Qed.

(** Federer (1969), 1.10.5, p. 48: monomials in dual one-forms. This
    interface restricts the actual graded product from 1.10.2 to its total
    degree. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom BoundedHom LinearBasis SymmetricAlgebra SymmetricGrading
  SymmetricLowPowers SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials
  SymmetricDividedMonomials SymmetricForms SymmetricFormSum SymmetricPairing
  SymmetricDualMonomialProducts SymmetricMonomialCoordinates SymmetricMonomialTuples
  SymmetricOneFormUnitBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_dual_monomial_form]: Federer 1.10.5,
    p. 48, omega^alpha as a symmetric form of degree m,
    where the entries of alpha sum to m. *)
Definition symmetric_dual_monomial_form (K : fieldType) (V : lmodType K)
    n (omega : 'I_n -> S_m V K^o 1) m (a : symmetric_indices n m) : S_m V K^o m :=
  sform_component m (symmetric_one_form_monomial omega (symmetric_indices_unbound a)).

(** Source for [symmetric_dual_monomial_as_product]: Federer
    1.10.5, p. 48, supporting identification: omega^alpha
    is the product of the one-forms in its repeated-index tuple. *)
Lemma symmetric_dual_monomial_as_product (K : fieldType) (V : lmodType K)
    n (omega : 'I_n -> S_m V K^o 1) m (a : symmetric_indices n m) :
  symmetric_dual_monomial_form omega a = symmetric_one_form_product_form
    (fun i => omega (tnth (symmetric_monomial_tuple idfun a) i)).
Proof.
rewrite /symmetric_dual_monomial_form /symmetric_one_form_monomial
  /symmetric_one_form_word /symmetric_one_form_product_form.
congr (sform_component _ (foldr _ _ _)).
have hh := @map_comp _ _ _ (fun j => sform_include (omega j))
  (tnth (symmetric_monomial_tuple idfun a)) (enum 'I_m).
rewrite map_tnth_enum in hh; exact: esym hh.
Qed.

(** Source for [symmetric_dual_monomial_diagonal]: Federer
    1.10.5, p. 48, supporting lower bounds: the product
    omega^alpha takes the value alpha! on e^alpha for a dual
    pair of bases. This is the pairing formula of 1.10.2, p. 45. *)
Lemma symmetric_dual_monomial_diagonal (K : fieldType) (h0 : [pchar K] =i pred0)
    (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
    (omega : 'I_n -> S_m V K^o 1)
    (hd : forall i j, symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) =
      if j==i then 1 else 0) m (a : symmetric_indices n m) :
  symmetric_dual_monomial_form omega a (symmetric_monomial_tuple e a) =
    (symmetric_multi_factorial (symmetric_indices_unbound a))%:R.
Proof.
rewrite /symmetric_dual_monomial_form sform_componentE
  (@symmetric_one_form_monomial_coordinate K V n omega e he h0 hd).
change (symmetric_coordinate_full_form he (symmetric_indices_unbound a)
  (symmetric_monomial e (symmetric_indices_unbound a)) =
  (symmetric_multi_factorial (symmetric_indices_unbound a))%:R).
by rewrite symmetric_coordinate_full_formE symmetric_monomial_coordinateE eqxx mulr1.
Qed.

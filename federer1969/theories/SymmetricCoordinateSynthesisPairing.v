(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the original coordinate form sum has its prescribed monomial
    coefficients. Reuse the divided-monomial duality of 1.10.2, p. 45. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom HomogeneousHom BoundedHom LinearBasis FiniteDualDimension
  SymmetricForms SymmetricFormIsomorphism SymmetricPairing SymmetricMultiIndices
  SymmetricIndexBounds SymmetricDividedBasis SymmetricCoordinateDualBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_coordinate_synthesis_pairing]: supporting
    finite Taylor interpolation for Federer 3.4.8(5), p. 328.
    The finite original coordinate-form sum recovers each coefficient
    on the corresponding divided monomial, by 1.10.2, p. 45. *)
Lemma symmetric_coordinate_synthesis_pairing (K:fieldType)
    (h0:[pchar K] =i pred0) (X:lmodType K) n (e:'I_n->X) (he:is_basis e) k
    (c:symmetric_indices n k->K) (b:symmetric_indices n k):
  symmetric_pairing (symmetric_divided_basis_vector e b)
    (\sum_(a:symmetric_indices n k) c a *: symmetric_coordinate_basis_form he k a) = c b.
Proof.
have hMap:sform_to_hom
    (\sum_(a:symmetric_indices n k) c a *: symmetric_coordinate_basis_form he k a) =
    \sum_(a:symmetric_indices n k) c a *:
      @dual_basis K (Finite.clone (symmetric_indices n k) _) _ _
        (symmetric_divided_basis h0 he k) a.
  rewrite linear_sum;apply:eq_bigr=>a _.
  rewrite linearZ.
  exact:(congr1 (fun h=>c a *:h)
    (@symmetric_coordinate_basis_to_hom K h0 X n e he k a)).
by rewrite /symmetric_pairing hMap dual_sum_evaluate.
Qed.

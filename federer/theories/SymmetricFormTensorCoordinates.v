(** Federer (1969), 1.10.6, p. 49: the displayed tensor associated with a
    symmetric form, expressed using the dual normalized monomial bases. The
    construction is independent of the auxiliary basis and preserves the
    specified inner product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorMaps Hom HomTensor
  LinearBasis FiniteDualDimension InnerProductUP InnerSymmetricPolarity
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricPairing SymmetricNormalizedMonomials SymmetricNormalizedDualMonomials
  SymmetricMultiIndices SymmetricIndexBounds SymmetricFormTensor SymmetricFormInner
  SymmetricFormInnerCoordinates ScalarInnerProduct OrthonormalFamilies
  TensorInner TensorInnerContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable m : nat.
Local Notation omega := (fun i => inner_symmetric_polarity hB (e i)).
Local Notation hm := (symmetric_normalized_monomial_basis he m).

(** Source for [symmetric_normalized_dual_functional]: Federer 1.10.6,
    p. 49, the functional dual to a normalized primal monomial
    corresponds exactly to the normalized product of the dual one-forms. *)
Lemma symmetric_normalized_dual_functional (a : symmetric_indices n m) :
  hom_to_sform (dual_basis hm a) = symmetric_normalized_dual_monomial omega a.
Proof.
apply: (can_inj (@sform_to_homK R V R^o m)); rewrite hom_to_sformK.
apply: hom_ext=> x.
apply: (basis_linear_ext hm (hom_as_linear (dual_basis hm a))
  (hom_as_linear (sform_to_hom (symmetric_normalized_dual_monomial omega a)))) x=> b.
rewrite !hom_as_linearE dual_basisE.
symmetry; exact: (@symmetric_normalized_dual_pairing R V B hB n e ho m a b).
Qed.

(** Source for [symmetric_form_tensor_orthonormal_sum]: Federer 1.10.6,
    p. 49, the first displayed sum: the associated tensor is
    the sum of normalized dual monomials tensor the form's evaluations
    on the matching normalized primal monomials. *)
Theorem symmetric_form_tensor_orthonormal_sum (f : S_m V W m) :
  symmetric_form_tensor he f =
    \sum_(a : symmetric_indices n m)
      tensor_inj (symmetric_normalized_dual_monomial omega a)
        (symmetric_pairing (symmetric_normalized_monomial e a) f).
Proof.
change (symmetric_covector_tensor_from_hom (Hom_tensor hm (sform_to_hom f)) =
  \sum_(a : symmetric_indices n m)
    tensor_inj (symmetric_normalized_dual_monomial omega a)
      (symmetric_pairing (symmetric_normalized_monomial e a) f)).
rewrite /Hom_tensor linear_sum.
apply: eq_bigr=> a _.
rewrite /symmetric_covector_tensor_from_hom tensor_mapE.
change (tensor_inj (hom_to_sform (dual_basis hm a))
    (symmetric_pairing (symmetric_normalized_monomial e a) f) =
  tensor_inj (symmetric_normalized_dual_monomial omega a)
    (symmetric_pairing (symmetric_normalized_monomial e a) f)).
by rewrite symmetric_normalized_dual_functional.
Qed.

Variable C : W -> W -> R.
Hypothesis hC : is_inner_product C.

(** Source for [symmetric_form_tensor_isometry]: Federer 1.10.6,
    pp. 48-49, the tensor identification used to define the
    inner product is an isometry. This verifies compatibility with the
    tensor of the scalar form metric and the given coefficient metric. *)
Theorem symmetric_form_tensor_isometry (f g : S_m V W m) :
  tensor_inner (symmetric_form_inner_productP hB (scalar_inner_productP R) he m) hC
    (symmetric_form_tensor he f) (symmetric_form_tensor he g) =
      symmetric_form_inner hB hC he m f g.
Proof.
rewrite !symmetric_form_tensor_orthonormal_sum.
rewrite (@tensor_inner_orthonormal_contraction R (S_m V R^o m) W
  (symmetric_form_inner hB (scalar_inner_productP R) he m) C
  (symmetric_form_inner_productP hB (scalar_inner_productP R) he m) hC
  (Finite.clone (symmetric_indices n m) _)
  (@symmetric_normalized_dual_monomial R V n omega m)
  (@symmetric_normalized_dual_orthonormal R V B hB n e he ho m)).
symmetry; exact: (@symmetric_form_inner_orthonormal_sum R V W B C hB hC
  n e he n e he ho m f g).
Qed.
End Coordinates.

(** Source for [symmetric_form_tensor_basis_independent]: Federer 1.10.6,
    pp. 48-49, supporting intrinsicness: the tensor associated
    with a form does not depend on the supplied finite basis. *)
Theorem symmetric_form_tensor_basis_independent (R : rcfType) (V W : lmodType R)
    n (e : 'I_n -> V) (he : is_basis e)
    k (b : 'I_k -> V) (hb : is_basis b) m (f : S_m V W m) :
  symmetric_form_tensor he f = symmetric_form_tensor hb f.
Proof.
apply: (can_inj (@tensor_symmetric_formK R V W m n e he)).
by rewrite !symmetric_form_tensorK.
Qed.

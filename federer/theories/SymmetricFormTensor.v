(** Federer (1969), 1.10.6, pp. 48-49: the canonical identification of
    symmetric W-valued forms with scalar symmetric forms tensor W. It is the
    Hom-tensor identification of 1.1.4 composed with the form-Hom
    isomorphisms of 1.10.1. Only the input space is assumed finite
    dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorMaps TensorSpan Hom HomTensor
  LinearBasis SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricNormalizedMonomials SymmetricMultiIndices SymmetricIndexBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Tensor.
Variable R : rcfType.
Variables V W : lmodType R.
Variable m : nat.
Local Notation P := (symmetric_power V m).
Local Notation F := (S_m V R^o m).
Local Notation A := (S_m V W m).
Local Notation T := (tensor_space F W).

(** Source for [symmetric_covector_tensor_to_hom]: Federer 1.10.6,
    p. 49, supporting factorwise transport: identify each scalar
    symmetric form with its functional on the symmetric power. *)
Definition symmetric_covector_tensor_to_hom :
    {linear T -> tensor_space (Hom P R^o) W} :=
  tensor_map (@sform_to_hom R V R^o m) (linear_id W).

(** Source for [symmetric_covector_tensor_from_hom]: Federer 1.10.6,
    p. 49, the inverse factorwise transport, using the proved
    inverse identification of scalar forms and functionals. *)
Definition symmetric_covector_tensor_from_hom :
    {linear tensor_space (Hom P R^o) W -> T} :=
  tensor_map (@hom_to_sform R V R^o m) (linear_id W).

(** Source for [symmetric_covector_tensor_to_homK]: Federer 1.10.6,
    p. 49, supporting cancellation of the factorwise identification. *)
Lemma symmetric_covector_tensor_to_homK :
  cancel symmetric_covector_tensor_to_hom symmetric_covector_tensor_from_hom.
Proof.
apply: tensor_induction=> [|x y hx hy|c x hx|f w].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- rewrite /symmetric_covector_tensor_to_hom /symmetric_covector_tensor_from_hom !tensor_mapE.
  change (tensor_inj (hom_to_sform (sform_to_hom f)) w = tensor_inj f w).
  by rewrite sform_to_homK.
Qed.

(** Source for [symmetric_covector_tensor_from_homK]: Federer 1.10.6,
    p. 49, supporting cancellation in the reverse direction. *)
Lemma symmetric_covector_tensor_from_homK :
  cancel symmetric_covector_tensor_from_hom symmetric_covector_tensor_to_hom.
Proof.
apply: tensor_induction=> [|x y hx hy|c x hx|f w].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- rewrite /symmetric_covector_tensor_to_hom /symmetric_covector_tensor_from_hom !tensor_mapE.
  change (tensor_inj (sform_to_hom (hom_to_sform f)) w = tensor_inj f w).
  by rewrite hom_to_sformK.
Qed.

(** Source for [tensor_symmetric_form]: Federer 1.10.6,
    p. 49, the natural linear map from scalar forms tensor W
    to W-valued symmetric forms. It needs no basis or finite dimension. *)
Definition tensor_symmetric_form : {linear T -> A} :=
  linear_comp (@hom_to_sform R V W m)
    (linear_comp (@tensor_Hom R P W) symmetric_covector_tensor_to_hom).

(** Source for [tensor_symmetric_formE]: Federer 1.10.6,
    p. 49, a pure tensor a tensor w evaluates on a tuple
    as a(tuple) times w, characterizing the natural identification. *)
Lemma tensor_symmetric_formE (a : F) w t :
  tensor_symmetric_form (tensor_inj a w) t = (a t : R) *: w.
Proof.
change (hom_to_sform (@tensor_Hom R P W (symmetric_covector_tensor_to_hom (tensor_inj a w))) t = (a t : R) *: w).
rewrite /symmetric_covector_tensor_to_hom tensor_mapE hom_to_sformE tensor_HomE
  sform_to_hom_tuple.
by [].
Qed.

Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation hm := (symmetric_normalized_monomial_basis he m).

(** Source for [symmetric_form_tensor]: Federer 1.10.6,
    p. 49, the tensor associated with a W-valued symmetric form,
    obtained through the already proved Hom-tensor isomorphism. *)
Definition symmetric_form_tensor : {linear A -> T} :=
  linear_comp symmetric_covector_tensor_from_hom
    (linear_comp (@Hom_tensor R P W (Finite.clone (symmetric_indices n m) _)
      _ hm) (@sform_to_hom R V W m)).

(** Source for [symmetric_form_tensorK]: Federer 1.10.6,
    p. 49, converting the associated tensor back recovers the form. *)
Lemma symmetric_form_tensorK : cancel symmetric_form_tensor tensor_symmetric_form.
Proof.
move=> f; change (hom_to_sform (@tensor_Hom R P W
  (symmetric_covector_tensor_to_hom (symmetric_covector_tensor_from_hom
    (Hom_tensor hm (sform_to_hom f))))) = f).
by rewrite symmetric_covector_tensor_from_homK Hom_tensorK sform_to_homK.
Qed.

(** Source for [tensor_symmetric_formK]: Federer 1.10.6,
    p. 49, the identification is onto the whole tensor product,
    including an arbitrary dimensional coefficient space. *)
Lemma tensor_symmetric_formK : cancel tensor_symmetric_form symmetric_form_tensor.
Proof.
move=> t; change (symmetric_covector_tensor_from_hom
  (Hom_tensor hm (sform_to_hom (hom_to_sform
    (@tensor_Hom R P W (symmetric_covector_tensor_to_hom t))))) = t).
by rewrite hom_to_sformK tensor_HomK symmetric_covector_tensor_to_homK.
Qed.
End Tensor.
Arguments symmetric_form_tensor {R V W m n e} he.
Arguments tensor_symmetric_form {R V W m}.
Arguments symmetric_covector_tensor_to_hom {R V W m}.
Arguments symmetric_covector_tensor_from_hom {R V W m}.

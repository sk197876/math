(** Federer (1969), 1.7.3, pp. 29-30: sealed existence of orthonormal skew
    blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP LinearBasis SymmetricEndomorphisms
  OrthonormalFamilies SkewNormalFormUP SkewNormalFormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SkewNormalFormSig.
(** Source for [exists_blocks]: Federer 1.7.3, pp. 29-30,
    orthonormal pairs and nonnegative coefficients specified solely
    by their equality with the bilinear form of the skew map. *)
Parameter exists_blocks : forall (R : realType) (V : lmodType R)
    (B : V -> V -> R), is_inner_product B ->
    forall n (b : 'I_n -> V), is_basis b ->
    forall f : {linear V -> V}, is_skewsymmetric_endomorphism B f ->
    exists m (a c : 'I_m -> V) (lambda : 'I_m -> R),
      orthonormal_family B (paired_family a c) /\
      (forall i, 0 <= lambda i) /\
      forall x y, B (f x) y = \sum_i lambda i * skew_pair_form B (a i) (c i) x y.
End SkewNormalFormSig.
Module SkewNormalForm : SkewNormalFormSig.
(** Source for [exists_blocks]: Federer 1.7.3, pp. 29-30,
    the private invariant-subspace proof supplies the specified blocks. *)
Theorem exists_blocks (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f : {linear V -> V}) (hf : is_skewsymmetric_endomorphism B f) :
    exists m (a c : 'I_m -> V) (lambda : 'I_m -> R),
      orthonormal_family B (paired_family a c) /\
      (forall i, 0 <= lambda i) /\
      forall x y, B (f x) y = \sum_i lambda i * skew_pair_form B (a i) (c i) x y.
Proof. exact: (@skew_normal_witness R V B hB n b hb f hf). Qed.
End SkewNormalForm.

(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP FamilyUpdate TensorFamilyUP TensorFamilyBinary
  TensorFamilyConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The tensor product of V_1, …, V_m used in the sequel. The signature
    exposes only the space, the m-linear map and its universal property;
    the opaque ascription below hides the construction, so later results
    depend on the universal property alone. *)
Module Type TensorFamilySig.
(** Source for [tensor_family]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_family :
  forall (K : fieldType) (m : nat), ('I_m -> lmodType K) -> lmodType K.
(** Source for [tensor_family_mul]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_family_mul :
  forall (K : fieldType) (m : nat) (V : 'I_m -> lmodType K),
  {dffun forall i, V i} -> tensor_family V.
(** Source for [tensor_familyP]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Sealed interface specification for this
    passage; the implementation proves this obligation. *)
Parameter tensor_familyP :
  forall (K : fieldType) (m : nat) (V : 'I_m -> lmodType K),
  is_tensor_product_family (@tensor_family_mul K m V).
End TensorFamilySig.

Module TensorFamilyImpl <: TensorFamilySig.
(** Source for [tensor_family]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_family (K : fieldType) (m : nat) (V : 'I_m -> lmodType K) :
    lmodType K :=
  GRing.Lmodule.clone K (family_tensor_space V) _.
(** Source for [tensor_family_mul]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_family_mul (K : fieldType) (m : nat) (V : 'I_m -> lmodType K) :
    {dffun forall i, V i} -> tensor_family V :=
  @family_tensor_inj K m V.
(** Source for [tensor_familyP]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_familyP (K : fieldType) (m : nat) (V : 'I_m -> lmodType K) :
    is_tensor_product_family (@tensor_family_mul K m V) :=
  tensor_family_exists V.
End TensorFamilyImpl.

Module TensorFamilySealed : TensorFamilySig := TensorFamilyImpl.
Export TensorFamilySealed.
Arguments tensor_family {K m} V.
Arguments tensor_family_mul {K m} V x.
Arguments tensor_familyP {K m} V.

(** Source for [is_tensor_product_family_eq]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma is_tensor_product_family_eq (K : fieldType) (m : nat) (V : 'I_m -> lmodType K)
    (T : lmodType K) (mu mu' : {dffun forall i, V i} -> T) :
  (forall x, mu x = mu' x) -> is_tensor_product_family mu ->
  is_tensor_product_family mu'.
Proof.
move=> e [hmu hu]; constructor.
  by move=> x i a v w; rewrite -!e hmu.
move=> Z beta hb; have [f [hf hg]] := hu Z beta hb.
exists f; split.
  by move=> x; rewrite -e hf.
by move=> g hg'; apply: hg => x; rewrite e hg'.
Qed.

(** Federer 1.1.1 for two factors: V ⊗ W is the case of the family (V, W). *)
Section Binary.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [tensor]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition tensor : lmodType K := tensor_family (pair_family V W).
(** Source for [tensor_mul]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition tensor_mul (v : V) (w : W) : tensor :=
  tensor_family_mul (pair_family V W) (family_pair v w).

(** Source for [tensorP]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensorP : is_tensor_product tensor_mul.
Proof.
apply/tensor_product_family_pair.
apply: (is_tensor_product_family_eq _ (tensor_familyP (pair_family V W))).
by move=> x; rewrite /uncurry_pair /tensor_mul family_pair_eta.
Qed.
End Binary.

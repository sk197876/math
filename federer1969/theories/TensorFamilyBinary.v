(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP FamilyUpdate TensorFamilyUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.1 for m = 2: the binary universal property is the case of
    the family (V, W) indexed by 'I_2. *)
Section PairFamily.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [pair_component]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition pair_component (b : bool) : lmodType K := if b then V else W.
(** Source for [pair_family]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition pair_family (i : 'I_2) : lmodType K := pair_component (val i == 0%N).

(** Source for [ord1]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition ord1 : 'I_2 := Ordinal (isT : 1 < 2)%N.

(** Source for [ord2_rect]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma ord2_rect (P : 'I_2 -> Type) : P ord0 -> P ord1 -> forall i, P i.
Proof.
move=> h0 h1 [[|[|k]] hi].
- by have -> : Ordinal hi = ord0 by exact: val_inj.
- by have -> : Ordinal hi = ord1 by exact: val_inj.
- by exfalso.
Qed.

(** Source for [ord01]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma ord01 : ord0 != ord1 :> 'I_2.
Proof. by []. Qed.

(** Source for [family_pair]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition family_pair (v : V) (w : W) : {dffun forall i, pair_family i} :=
  [ffun i => if val i == 0%N as b return pair_component b then v else w].

(** Source for [family_pair0]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_pair0 v w : family_pair v w ord0 = v.
Proof. by rewrite ffunE. Qed.

(** Source for [family_pair1]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_pair1 v w : family_pair v w ord1 = w.
Proof. by rewrite ffunE. Qed.

(** Source for [family_pair_eta]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_pair_eta (x : {dffun forall i, pair_family i}) :
  family_pair (x ord0) (x ord1) = x.
Proof.
apply/ffunP; elim/ord2_rect.
  exact: family_pair0.
exact: family_pair1.
Qed.

(** Source for [family_pair_with0]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_pair_with0 x (v : V) :
  family_with x (v : pair_family ord0) = family_pair v (x ord1).
Proof.
apply/ffunP; elim/ord2_rect.
  by rewrite family_with_in family_pair0.
by rewrite family_with_out // family_pair1.
Qed.

(** Source for [family_pair_with1]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_pair_with1 x (w : W) :
  family_with x (w : pair_family ord1) = family_pair (x ord0) w.
Proof.
apply/ffunP; elim/ord2_rect.
  by rewrite family_with_out // family_pair0.
by rewrite family_with_in family_pair1.
Qed.

(** Source for [uncurry_pair]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition uncurry_pair (Z : lmodType K) (mu : V -> W -> Z)
    (x : {dffun forall i, pair_family i}) : Z :=
  mu (x ord0) (x ord1).

(** Source for [curry_pair]: Federer (1969), 1.1.1, p. 9, universal-property
    paragraph and the following uniqueness assertion. In words: Every
    multilinear map factors uniquely through the tensor product by a linear
    map; this characterises the tensor product up to a compatible linear
    isomorphism. Definition or construction used to formalise this passage. *)
Definition curry_pair (Z : lmodType K) (beta : {dffun forall i, pair_family i} -> Z)
    (v : V) (w : W) : Z :=
  beta (family_pair v w).

(** Source for [multilinear_uncurry]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_uncurry (Z : lmodType K) (mu : V -> W -> Z) :
  bilinear mu <-> multilinear (uncurry_pair mu).
Proof.
split.
  move=> [h1 h2] x; elim/ord2_rect=> a u u'; rewrite /uncurry_pair.
    by rewrite !family_with_in !family_with_out // h1.
  by rewrite !family_with_in !family_with_out // h2.
move=> h; split.
  move=> w a v v'.
  have := h (family_pair 0 w) ord0 a v v'.
  by rewrite /uncurry_pair !family_pair_with0 !family_pair0 !family_pair1.
move=> v a w w'.
have := h (family_pair v 0) ord1 a w w'.
by rewrite /uncurry_pair !family_pair_with1 !family_pair0 !family_pair1.
Qed.

(** Source for [uncurry_curry_pair]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma uncurry_curry_pair (Z : lmodType K) (beta : {dffun forall i, pair_family i} -> Z) x :
  uncurry_pair (curry_pair beta) x = beta x.
Proof. by rewrite /uncurry_pair /curry_pair family_pair_eta. Qed.

(** Source for [curry_uncurry_pair]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma curry_uncurry_pair (Z : lmodType K) (mu : V -> W -> Z) v w :
  curry_pair (uncurry_pair mu) v w = mu v w.
Proof. by rewrite /curry_pair /uncurry_pair family_pair0 family_pair1. Qed.

(** Source for [tensor_product_family_pair]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_product_family_pair (T : lmodType K) (mu : V -> W -> T) :
  is_tensor_product mu <-> is_tensor_product_family (uncurry_pair mu).
Proof.
split=> H.
  constructor; first exact/multilinear_uncurry/(tensor_bilinear H).
  move=> Z beta hb.
  have hb2 : bilinear (curry_pair beta).
    apply/multilinear_uncurry => x i a u u'.
    by rewrite !uncurry_curry_pair; exact: hb.
  have [f [hf hu]] := tensor_universal H hb2.
  exists f; split.
    by move=> x; rewrite /uncurry_pair hf -uncurry_curry_pair.
  move=> g hg; apply: hu => v w.
  by rewrite -curry_uncurry_pair /curry_pair hg.
constructor.
  apply/multilinear_uncurry; exact: (tensor_family_multilinear H).
move=> Z beta hb.
have [f [hf hu]] := tensor_family_universal H
  (iffLR (multilinear_uncurry beta) hb).
exists f; split.
  move=> v w; have := hf (family_pair v w).
  by rewrite /uncurry_pair !family_pair0 !family_pair1.
move=> g hg; apply: hu => x.
by rewrite /uncurry_pair hg.
Qed.
End PairFamily.

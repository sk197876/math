(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP FamilyUpdate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.1: m-linear maps and the universal property of the tensor
    product of V_1, …, V_m. The factors are recorded by the domain of the
    m-linear map; the interface is independent of any construction. *)
Section UniversalProperty.
Variable K : fieldType.
Variable m : nat.
Variable V : 'I_m -> lmodType K.

(** Source for [multilinear]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Definition or construction used to
    formalise this passage. *)
Definition multilinear (Z : lmodType K) (mu : {dffun forall i, V i} -> Z) : Prop :=
  forall x i, linear (fun v : V i => mu (family_with x v)).

(** Source for [is_tensor_product_family]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Record is_tensor_product_family (T : lmodType K)
    (mu : {dffun forall i, V i} -> T) : Prop := {
  tensor_family_multilinear : multilinear mu;
  tensor_family_universal :
    forall (Z : lmodType K) (beta : {dffun forall i, V i} -> Z), multilinear beta ->
    exists f : {linear T -> Z},
      (forall x, f (mu x) = beta x) /\
      (forall g : {linear T -> Z},
        (forall x, g (mu x) = beta x) -> forall t, g t = f t)
}.

(** Source for [multilinear_post]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma multilinear_post (T Z : lmodType K) (mu : {dffun forall i, V i} -> T)
    (f : {linear T -> Z}) :
  multilinear mu -> multilinear (fun x => f (mu x)).
Proof. by move=> h x i a v w; rewrite (h x i) linearP. Qed.

(** Source for [tensor_family_ext]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_family_ext (T : lmodType K) (mu : {dffun forall i, V i} -> T)
    (H : is_tensor_product_family mu) (Z : lmodType K)
    (f g : {linear T -> Z}) :
  (forall x, f (mu x) = g (mu x)) -> forall t, f t = g t.
Proof.
move=> e.
have [h [hmu huniq]] := tensor_family_universal H
  (multilinear_post g (tensor_family_multilinear H)).
by move=> t; rewrite (huniq f e) (huniq g (fun x => erefl _)).
Qed.
End UniversalProperty.
Arguments tensor_family_ext {K m V T mu} H {Z} f g _ t.

(** Federer 1.1.1: two tensor products of V_1, …, V_m are isomorphic by a
    unique linear isomorphism compatible with the m-linear maps. *)
Section Uniqueness.
Variable K : fieldType.
Variable m : nat.
Variable V : 'I_m -> lmodType K.
Variables T T' : lmodType K.
Variables (mu : {dffun forall i, V i} -> T) (mu' : {dffun forall i, V i} -> T').
Hypotheses (H : is_tensor_product_family mu) (H' : is_tensor_product_family mu').

(** Source for [tensor_family_unique]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_family_unique :
  exists (f : {linear T -> T'}) (g : {linear T' -> T}),
    (forall x, f (mu x) = mu' x) /\
    (forall x, g (mu' x) = mu x) /\
    cancel f g /\ cancel g f /\
    (forall f' : {linear T -> T'},
      (forall x, f' (mu x) = mu' x) -> forall t, f' t = f t).
Proof.
have [f [fmu fu]] := tensor_family_universal H (tensor_family_multilinear H').
have [g [gmu gu]] := tensor_family_universal H' (tensor_family_multilinear H).
exists f, g; split=> //; split=> //; split.
  apply: (tensor_family_ext H (linear_comp g f) (linear_id T)) => x /=.
  by rewrite fmu gmu.
split.
  apply: (tensor_family_ext H' (linear_comp f g) (linear_id T')) => x /=.
  by rewrite gmu fmu.
exact: fu.
Qed.
End Uniqueness.

(** Federer 1.1.1: linear maps f_i : V_i → W_i induce a linear map of the
    tensor products, characterised by its values on m-fold products. *)
(** Source for [tensor_family_map_spec]: Federer (1969), 1.1.1, p. 9,
    universal-property paragraph and the following uniqueness assertion. In
    words: Every multilinear map factors uniquely through the tensor product
    by a linear map; this characterises the tensor product up to a
    compatible linear isomorphism. Definition or construction used to
    formalise this passage. *)
Definition tensor_family_map_spec (K : fieldType) (m : nat)
    (U V : 'I_m -> lmodType K) (TU TV : lmodType K)
    (muU : {dffun forall i, U i} -> TU) (muV : {dffun forall i, V i} -> TV)
    (f : forall i, {linear U i -> V i}) (F : {linear TU -> TV}) : Prop :=
  forall x, F (muU x) = muV (family_map f x).

Section Naturality.
Variable K : fieldType.
Variable m : nat.
Variables U V W : 'I_m -> lmodType K.
Variables (TU TV TW : lmodType K).
Variables (muU : {dffun forall i, U i} -> TU) (muV : {dffun forall i, V i} -> TV)
  (muW : {dffun forall i, W i} -> TW).
Hypotheses (HU : is_tensor_product_family muU) (HV : is_tensor_product_family muV).

(** Source for [multilinear_family_map]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph and displayed formula. In words: Linear maps on the
    factors induce a unique linear map of tensor products sending each pure
    tensor to the tensor of the images. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma multilinear_family_map (Z : lmodType K) (mu : {dffun forall i, V i} -> Z)
    (f : forall i, {linear U i -> V i}) :
  multilinear mu -> multilinear (fun x => mu (family_map f x)).
Proof.
move=> h x i a u u'.
by rewrite !family_map_with linearP (h (family_map f x) i).
Qed.

(** Source for [tensor_family_map_exists]: Federer (1969), 1.1.1, p. 9,
    final naturality paragraph and displayed formula. In words: Linear maps
    on the factors induce a unique linear map of tensor products sending
    each pure tensor to the tensor of the images. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_family_map_exists (f : forall i, {linear U i -> V i}) :
  exists F : {linear TU -> TV}, tensor_family_map_spec muU muV f F.
Proof.
have [F [hF _]] := tensor_family_universal HU
  (multilinear_family_map f (tensor_family_multilinear HV)).
by exists F.
Qed.

(** Source for [tensor_family_map_unique]: Federer (1969), 1.1.1, p. 9,
    final naturality paragraph and displayed formula. In words: Linear maps
    on the factors induce a unique linear map of tensor products sending
    each pure tensor to the tensor of the images. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_family_map_unique (f : forall i, {linear U i -> V i})
    (F G : {linear TU -> TV}) :
  tensor_family_map_spec muU muV f F -> tensor_family_map_spec muU muV f G ->
  forall t, F t = G t.
Proof.
move=> hF hG; apply: (tensor_family_ext HU) => x.
by rewrite hF hG.
Qed.

(** Source for [tensor_family_map_id]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph. In words: The maps induced on tensor products act
    componentwise on pure tensors; identities and composition therefore pass
    to tensor products. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_family_map_id (F : {linear TV -> TV}) :
  tensor_family_map_spec muV muV (fun i => linear_id (V i)) F -> forall t, F t = t.
Proof.
move=> hF; apply: (tensor_family_ext HV F (linear_id TV)) => x /=.
rewrite hF; congr muV; apply/ffunP=> i.
by rewrite family_mapE.
Qed.

(** Source for [tensor_family_map_comp]: Federer (1969), 1.1.1, p. 9, final
    naturality paragraph. In words: The maps induced on tensor products act
    componentwise on pure tensors; identities and composition therefore pass
    to tensor products. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_family_map_comp (f : forall i, {linear U i -> V i})
    (g : forall i, {linear V i -> W i}) (F : {linear TU -> TV})
    (G : {linear TV -> TW}) (GF : {linear TU -> TW}) :
  tensor_family_map_spec muU muV f F -> tensor_family_map_spec muV muW g G ->
  tensor_family_map_spec muU muW (fun i => linear_comp (g i) (f i)) GF ->
  forall t, GF t = G (F t).
Proof.
move=> hF hG hGF.
apply: (tensor_family_ext HU GF (linear_comp G F)) => x /=.
rewrite hGF hF hG; congr muW; apply/ffunP=> i.
by rewrite !family_mapE.
Qed.
End Naturality.

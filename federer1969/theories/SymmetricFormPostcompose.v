(** Federer (1969), 1.10.5, p. 48: supporting scalarization of a
    vector-valued symmetric form by a linear functional on the coefficient
    space. This uses the multilinear definition in 1.10.1, pp. 43-44. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import AlternatingForms SymmetricForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_form_postcompose]: Federer 1.10.5,
    p. 48, supporting postcomposition with a coefficient-space
    linear map. Multilinearity and symmetry follow directly from the
    original form and the linear-map laws, in every degree. *)
Definition symmetric_form_postcompose (K : fieldType) (V W Z : lmodType K)
    (g : {linear W -> Z}) m (f : S_m V W m) : S_m V Z m.
Proof.
apply: (@SymmetricForm K V Z m (fun t=>g (f t))); apply/asboolP; split.
- move=> s t h a x y; rewrite (@sform_multilinear K V W m f s t h) linearD linearZ; by [].
- move=> s t hp; by rewrite (@sform_tuple_symmetric K V W m f s t hp).
Defined.

(** Source for [symmetric_form_postcomposeE]: Federer 1.10.5,
    p. 48, supporting evaluation identity for the scalarized
    form, retaining the actual tuple of input vectors. *)
Lemma symmetric_form_postcomposeE (K : fieldType) (V W Z : lmodType K)
    (g : {linear W -> Z}) m (f : S_m V W m) t :
  symmetric_form_postcompose g f t=g (f t).
Proof. by []. Qed.

(** Federer (1969), 1.10.5, p. 48: supporting list and two-slot identities
    for the Hilbert-input norm equality. These derive from the actual
    symmetric multilinear forms of 1.10.1, pp. 43-44. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import TensorUP Bilinear BilinearNegation InnerProductUP
  SymmetricForms SymmetricFormWords RealNormUP SymmetricOperatorNorm
  SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_form_front_bilinear]: Federer 1.10.5,
    p. 48, supporting two-slot slice of a symmetric form.
    Fixing all arguments after the first two gives a bilinear map;
    the word extension also covers other list lengths by zero. *)
Lemma symmetric_form_front_bilinear (K : fieldType) (V W : lmodType K)
    m (f : S_m V W m) (s : seq V) :
  bilinear (fun x y=>sform_words f (x::y::s)).
Proof.
split.
- move=> y; exact (@sform_words_multilinear K V W m f [::] (y::s)).
- move=> x; exact (@sform_words_multilinear K V W m f [::x] s).
Qed.

(** Source for [symmetric_form_front_symmetric]: Federer 1.10.5,
    p. 48, supporting symmetry of the two-slot slice, directly
    from permutation invariance of the original form. *)
Lemma symmetric_form_front_symmetric (K : fieldType) (V : lmodType K)
    m (f : S_m V K^o m) (s : seq V) :
  is_symmetric_bilinear (fun x y=>sform_words f (x::y::s)).
Proof.
split; first exact: symmetric_form_front_bilinear.
move=> x y; apply: (@sform_words_symmetric K V K^o m f (x::y::s) (y::x::s)).
change (perm_eq ([::x]++[::y]++s) ([::y]++[::x]++s)).
by rewrite perm_catCA.
Qed.

(** Source for [symmetric_form_word_norm_bound]: Federer
    1.10.5, p. 47, supporting homogeneous evaluation bound
    on a list of the correct length. The source form and input norms
    remain unchanged by the conversion from lists to tuples. *)
Lemma symmetric_form_word_norm_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV)
    (hW : is_real_seminorm NW) m (f : S_m V W m) L :
  (symmetric_operator_norm (proj1 hV) NW f<=L%:E)%E -> forall s,
  size s=m -> NW (sform_words f s)<=L*\prod_(x<-s) NV x.
Proof.
move=> hL s hs.
have ht : size s==m := introT eqP hs.
pose t : m.-tuple V := Tuple ht.
have hh := @symmetric_operator_finite_tuple_bound R V W NV NW hV hW m f L hL t.
rewrite -sform_wordsE -(@big_tuple R 1 *%R V m t predT NV) in hh.
exact hh.
Qed.

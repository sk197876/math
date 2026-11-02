(** Federer (1969), 3.1.24, p. 239: bound
    an outer differential on the word of inner values,
    using the tuple norm estimate of 1.10.5, p. 47. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom HomogeneousHom RealNormUP SymmetricAlgebra SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricOperatorNorm SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_operator_finite_word_bound]: supporting
    the bound for the outer derivative in Federer 3.1.24,
    p. 239. A finite operator bound M bounds the
    homogeneous extension on any word of the form's degree
    by M times the product of its argument lengths.
    This is the existing arbitrary-tuple bound, including an
    empty tuple, with its list representation made explicit. *)
Lemma symmetric_operator_finite_word_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_seminorm NY)
    m (phi:S_m X Y m) M :
  (symmetric_operator_norm hNX.1 NY phi<=M%:E)%E ->
  forall ys:seq X,size ys=m ->
    NY (sform_homogeneous phi (symmetric_word ys))<=M*\prod_(y<-ys) NX y.
Proof.
move=>hM ys hs.
pose t:m.-tuple X:=Tuple (introT eqP hs).
change (NY (sform_homogeneous phi (symmetric_word t))<=M*\prod_(y<-t) NX y).
rewrite sform_homogeneousE sform_extensionE sform_wordsE big_tuple.
exact (@symmetric_operator_finite_tuple_bound R X Y NX NY hNX hNY m phi M hM t).
Qed.

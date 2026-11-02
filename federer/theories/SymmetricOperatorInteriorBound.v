(** Federer (1969), 1.10.5, p. 47, the first inequality after the definition
    of the form norm. The estimate includes zero contracted factors and
    unbounded forms using nonnegative extended arithmetic. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import Hom HomogeneousHom GradedComponents RealNormUP
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricPairing
  SymmetricRightInterior SymmetricOperatorNormUP SymmetricOperatorNorm
  SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_right_interior_tupleE]: Federer 1.10.5,
    p. 47, supporting evaluation of a contraction by a product
    of vectors. It is the original form evaluated on the remaining
    arguments followed by the contracted arguments. This follows from
    the characteristic identity of 1.10.3, p. 45. *)
Lemma symmetric_right_interior_tupleE (K : fieldType) (V W : lmodType K)
    p q (hpq : (p<=q)%N) (a : p.-tuple V) (f : S_m V W q) (t : (q-p).-tuple V) :
  symmetric_right_interior hpq (symmetric_tuple_component a) f t =
    f (tcast (subnK hpq) [tuple of t ++ a]).
Proof.
rewrite -symmetric_pairing_tuple symmetric_right_interior_characteristic
  !symmetric_tuple_componentE sform_homogeneousE symmetric_word_cat sform_extensionE.
rewrite -sform_wordsE val_tcast; by [].
Qed.

Section Bound.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Variable NW : W -> R.
Hypothesis hV : is_real_norm NV.
Hypothesis hW : is_real_seminorm NW.
Local Notation hN := (proj1 hV).

(** Source for [symmetric_operator_interior_bound]: Federer 1.10.5,
    p. 47, the norm of contraction by a product of p vectors
    is at most their product of lengths times the original q-form norm,
    whenever p is at most q. Empty products and degree-zero outputs
    are included; no finite-dimensional hypothesis is imposed. *)
Theorem symmetric_operator_interior_bound p q (hpq : (p<=q)%N)
    (a : p.-tuple V) (f : S_m V W q) :
  (symmetric_operator_norm hN NW
      (symmetric_right_interior hpq (symmetric_tuple_component a) f) <=
    (\prod_(i < p) NV (tnth a i))%:E * symmetric_operator_norm hN NW f)%E.
Proof.
apply: symmetric_operator_norm_least=> t ht.
rewrite symmetric_right_interior_tupleE.
pose u := tcast (subnK hpq) [tuple of t ++ a].
have hh := @symmetric_operator_tuple_bound R V W NV NW hV hW q f u.
move: hh; rewrite -(@big_tuple R 1 *%R V q u predT NV) /u val_tcast /= big_cat
  (@big_tuple R 1 *%R V (q-p) t predT NV) (@big_tuple R 1 *%R V p a predT NV)=> hh.
apply: le_trans hh _; apply: lee_wpmul2r.
- exact (@symmetric_operator_norm_ge_zero R V W NV hN NW hW q f).
- rewrite lee_fin.
  have ha : 0 <= \prod_(i < p) NV (tnth a i).
    apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative hN (tnth a i).
  have ht1 : \prod_(i < q-p) NV (tnth t i) <= 1.
    have he : (\prod_(i < q-p) (1:R)) = 1 by rewrite prodr_const expr1n.
    rewrite -[X in _ <= X]he.
    apply: ler_prod=> i _; apply/andP; split.
    + exact: real_seminorm_nonnegative hN (tnth t i).
    + exact: ht.
  have hd := ler_wpM2r ha ht1; by rewrite mul1r in hd.
Qed.
End Bound.

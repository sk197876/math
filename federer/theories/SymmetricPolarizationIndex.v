(** Federer (1969), 1.9.3, p. 43: identifying the sole surviving multiindex
    in the polarization sum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricAlgebra SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricDividedMonomials SymmetricPolarizationCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polarization_one_index]: Federer 1.9.3,
    p. 43, the all-ones tuple regarded as an element of Xi(m,m). *)
Definition polarization_one_index m : symmetric_indices m m :=
  symmetric_indices_bound (Sub (symmetric_multi_one m) (introT eqP (symmetric_multi_one_degree m))).

(** Source for [polarization_one_indexE]: Federer 1.9.3,
    p. 43, its underlying tuple has every entry equal to one. *)
Lemma polarization_one_indexE m :
  symmetric_indices_unbound (polarization_one_index m) = symmetric_multi_one m.
Proof.
have h := @symmetric_indices_boundK m m
  (Sub (symmetric_multi_one m) (introT eqP (symmetric_multi_one_degree m))).
exact: (congr1 (fun z : symmetric_degree_indices m m => val z) h).
Qed.

(** Source for [polarization_one_index_test]: Federer 1.9.3,
    p. 43, testing the all-ones tuple is equivalent to testing
    the corresponding finite summation index. *)
Lemma polarization_one_index_test m (a : symmetric_indices m m) :
  (symmetric_indices_unbound a == symmetric_multi_one m) = (a == polarization_one_index m).
Proof.
apply/idP/idP=> /eqP h; apply/eqP.
- apply: (can_inj (@symmetric_indices_forgetK m m)); apply: val_inj.
  change (symmetric_indices_unbound a = symmetric_indices_unbound (polarization_one_index m)).
  by rewrite polarization_one_indexE.
- by rewrite h polarization_one_indexE.
Qed.

(** Source for [symmetric_multi_one_factorial]: Federer 1.9.3,
    p. 43, the factorial denominator of the all-ones tuple is one. *)
Lemma symmetric_multi_one_factorial m : symmetric_multi_factorial (symmetric_multi_one m) = 1%N.
Proof.
rewrite /symmetric_multi_factorial /symmetric_multi_one.
apply: big1=> i _; by rewrite ffunE.
Qed.

(** Source for [symmetric_monomial_word_one]: Federer 1.9.3,
    p. 43, the all-ones monomial word lists each vector once,
    in the original order. *)
Lemma symmetric_monomial_word_one (T : Type) m (v : 'I_m -> T) :
  symmetric_monomial_word v (symmetric_multi_one m) = [seq v i | i <- enum 'I_m].
Proof.
rewrite /symmetric_monomial_word /symmetric_multi_one.
elim: (enum 'I_m)=> [|i s ih] //=.
by rewrite ffunE /= ih.
Qed.

(** Source for [symmetric_divided_monomial_one]: Federer
    1.9.3, p. 43, the surviving divided monomial is the
    original product v_1 ... v_m because its denominator equals one. *)
Lemma symmetric_divided_monomial_one (K : fieldType) (V : lmodType K)
    m (v : 'I_m -> V) :
  symmetric_divided_monomial v (symmetric_multi_one m) =
    symmetric_word [seq v i | i <- enum 'I_m].
Proof.
by rewrite /symmetric_divided_monomial symmetric_multi_one_factorial invr1 scale1r
  /symmetric_monomial symmetric_monomial_word_one.
Qed.

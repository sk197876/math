(** Federer (1969), 3.1.24, p. 239: the unique
    outer-linear monomial in S(p) is the generator of the
    pth inner coefficient, with no other factors. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricAlgebra SymmetricMultiIndices SymmetricMonomials SymmetricExponentWords
  CompositionMultiIndices CompositionLinearIndex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_degree_one_symmetric_monomial]: the
    term Dg composed with D^p f is singled out from the
    inverse derivative formula in Federer 3.1.24, p. 239.
    In its inner symmetric monomial only the pth coefficient
    occurs, once. The proof uses the proved exponent counts
    and permutation invariance of symmetric words. *)
Lemma composition_degree_one_symmetric_monomial (K:fieldType) (V:lmodType K)
    k p (a:composition_indices k p) (e:nat->V) :
  symmetric_multi_degree (composition_indices_unbound a)= 1%N ->
  symmetric_monomial (fun i:'I_k=>e (val i).+1) (composition_indices_unbound a)=
    symmetric_generator (e p).
Proof.
move=>hd; have [i [hi [hai hz]]]:=composition_degree_one_support hd.
pose alpha:=composition_indices_unbound a.
have hc j:count_mem j (symmetric_monomial_word idfun alpha)=alpha j.
  have hh:=congr1 (fun z:symmetric_multi_index k=>z j) (symmetric_exponent_word_count_monomial alpha).
  by move:hh; rewrite /symmetric_exponent_word_count ffunE.
have hperm:perm_eq (symmetric_monomial_word idfun alpha) [::i].
  rewrite /perm_eq; apply/allP=>j _; apply/eqP; rewrite hc /= eq_sym.
  case hji:(j==i).
  - have he:j= i:=eqP hji; by rewrite he hai.
  - have hj:j!=i by rewrite hji.
    by rewrite (hz j hj).
have hmap:=perm_map (fun j:'I_k=>e (val j).+1) hperm.
rewrite symmetric_monomial_word_map /= hi in hmap.
rewrite /symmetric_monomial /symmetric_generator.
exact (symmetric_word_permutation hmap).
Qed.

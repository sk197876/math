(** Federer (1969), 3.1.24, p. 239: the
    outer derivative order in the coefficient sum is positive. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [composition_indices_positive_outer_degree]: supporting
    the positive-order scalar coefficients in Federer 3.1.24,
    p. 239. A nonnegative multiindex of positive weight
    has positive ordinary degree. All weights are positive;
    no zero-order derivative enters the displayed sum S(p). *)
Lemma composition_indices_positive_outer_degree k p (a:composition_indices k p) :
  (1<=p)%N -> (1<=symmetric_multi_degree (composition_indices_unbound a))%N.
Proof.
move=>hp.
case hd:(symmetric_multi_degree (composition_indices_unbound a))=>[|d]; last by [].
have hzero i:composition_indices_unbound a i= 0%N.
  have hh:=symmetric_multi_entry_bound (composition_indices_unbound a) i.
  by move:hh; rewrite hd leqn0=>/eqP.
have hw:composition_multi_weight (composition_indices_unbound a)= 0%N.
  rewrite /composition_multi_weight; apply: big1=>i _; by rewrite hzero muln0.
have hh:=composition_indices_weight a.
rewrite hw in hh; by rewrite -hh in hp.
Qed.

(** Federer (1969), 3.1.24, p. 239: removing
    the unique outer-linear term from S(p) leaves exactly
    the inverse remainder indices of outer degree greater than one. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices CompositionPositiveDegree CompositionLinearIndex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [composition_remainder_filter]: the distinction
    between the separated term Dg composed with D^p f and
    the sum over T(p) in Federer 3.1.24, p. 239.
    Positive weight makes the outer degree positive; uniqueness
    handles the only possible degree-one term. *)
Lemma composition_remainder_filter k p (a z:composition_indices k p) :
  1<=p -> symmetric_multi_degree (composition_indices_unbound z)= 1 ->
  (a!=z)=(1<symmetric_multi_degree (composition_indices_unbound a)).
Proof.
move=>hp hz; apply/idP/idP=>ha.
- have hpos:=composition_indices_positive_outer_degree a hp.
  have hne:symmetric_multi_degree (composition_indices_unbound a)!=1.
    apply/eqP=>hd.
    have he:a=z:=composition_degree_one_unique hd hz.
    by rewrite he eqxx in ha.
  by rewrite ltn_neqAle eq_sym hne hpos.
- apply/eqP=>he; by rewrite he hz ltnn in ha.
Qed.

(** Federer (1969), 3.1.24, p. 239: the set
    T(p) in the inverse derivative formula consists of the
    composition terms whose outer order is greater than one.
    Only strictly lower inner derivatives occur in those terms. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [composition_weight_degree_excess]: supporting
    the inverse sum T(p) in Federer 3.1.24, p. 239.
    Subtracting the ordinary degree from the weighted degree
    leaves the sum of the zero-based positions times their
    exponents; the equality avoids natural-number subtraction. *)
Lemma composition_weight_degree_excess k (a:symmetric_multi_index k) :
  composition_multi_weight a= symmetric_multi_degree a+\sum_(i<k) val i*a i.
Proof.
rewrite /composition_multi_weight /symmetric_multi_degree.
under eq_bigr do rewrite mulSn.
by rewrite big_split.
Qed.

(** Source for [composition_remainder_uses_lower_orders]: the
    indices in T(p) only use D^i f with i<p,
    Federer 3.1.24, p. 239. In any composition index
    of weight p and ordinary degree at least two, a positive
    exponent at position i forces i+1<p. *)
Lemma composition_remainder_uses_lower_orders k p (a:composition_indices k p) i :
  1<symmetric_multi_degree (composition_indices_unbound a) ->
  0<composition_indices_unbound a i -> (val i).+1<p.
Proof.
move=>hdeg hi.
pose alpha:=composition_indices_unbound a.
have hWeight:symmetric_multi_degree alpha+\sum_(j<k) val j*alpha j= p.
  by rewrite -composition_weight_degree_excess composition_indices_weight.
have hmul:val i<=val i*alpha i.
  have hh:=leq_mul (leqnn (val i)) hi.
  by rewrite muln1 in hh.
have hsum:val i*alpha i<=\sum_(j<k) val j*alpha j.
  by rewrite (bigD1 i) // leq_addr.
have hGain:symmetric_multi_degree alpha+val i<=p.
  rewrite -hWeight; exact (leq_add (leqnn _) (leq_trans hmul hsum)).
have hTwo:2+val i<=p:=leq_trans (leq_add hdeg (leqnn _)) hGain.
by rewrite add2n in hTwo.
Qed.

(** Source for [composition_remainder_last_exponent_zero]: the
    pth inner derivative is absent from the remainder sum
    in Federer 3.1.24, p. 239. Thus the degree-greater-
    than-one part of S(p) is exactly the printed lower-order
    indexing convention, with its final redundant exponent zero. *)
Lemma composition_remainder_last_exponent_zero p (a:composition_indices p.+1 p.+1) :
  1<symmetric_multi_degree (composition_indices_unbound a) ->
  composition_indices_unbound a ord_max=0.
Proof.
move=>hd.
case he:(composition_indices_unbound a ord_max)=>[|j]; first reflexivity.
have hpos:0<composition_indices_unbound a ord_max by rewrite he.
have hh:=composition_remainder_uses_lower_orders hd hpos.
by rewrite /= ltnn in hh.
Qed.

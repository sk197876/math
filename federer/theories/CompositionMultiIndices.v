(** Federer (1969), 3.1.11, p. 222: the index set S(p)
    in the formula for higher differentials of a composition.
    A k-term sequence has weight sum_i (i+1) alpha_i; this
    is distinct from its ordinary total degree sum_i alpha_i. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [composition_multi_weight]: the weighted equation
    defining S(p), Federer 3.1.11, p. 222. Positions start
    at zero here, so the printed weight i is represented by i+1. *)
Definition composition_multi_weight k (a : symmetric_multi_index k) :=
  \sum_(i<k) (val i).+1*a i.

(** Source for [composition_multi_degree_le_weight]: supporting
    finiteness of S(p) and the derivative order of the outer
    function in Federer 3.1.11, p. 222. Every weight is positive. *)
Lemma composition_multi_degree_le_weight k (a : symmetric_multi_index k) :
  symmetric_multi_degree a<=composition_multi_weight a.
Proof.
rewrite /symmetric_multi_degree /composition_multi_weight.
apply: leq_sum=>i _; by rewrite mulSn leq_addr.
Qed.

(** Source for [composition_multi_entry_le_weight]: each exponent
    of a term in S(p) is at most p, supporting the finite
    sum in Federer 3.1.11, p. 222. *)
Lemma composition_multi_entry_le_weight k (a : symmetric_multi_index k) i :
  a i<=composition_multi_weight a.
Proof.
exact: leq_trans (symmetric_multi_entry_bound a i) (composition_multi_degree_le_weight a).
Qed.

(** Source for [composition_indices]: the finite presentation
    of S(p), Federer 3.1.11, p. 222. The coordinate bound
    by p is redundant, as proved above. This predicate does
    not replace the weighted equation by an ordinary degree equation. *)
Definition composition_indices k p :=
  {a : {ffun 'I_k->'I_p.+1} | (\sum_(i<k) (val i).+1*val (a i))==p}.

(** Source for [composition_indices_unbound]: the underlying
    k-term sequence alpha of a member of S(p), Federer
    3.1.11, p. 222. *)
Definition composition_indices_unbound k p (a : composition_indices k p) :
    symmetric_multi_index k := [ffun i=>val (val a i)].

(** Source for [composition_indices_weight]: every displayed
    index has precisely weight p, Federer 3.1.11, p. 222. *)
Lemma composition_indices_weight k p (a : composition_indices k p) :
  composition_multi_weight (composition_indices_unbound a)=p.
Proof.
rewrite /composition_multi_weight /composition_indices_unbound.
under eq_bigr do rewrite ffunE.
exact: eqP (valP a).
Qed.

(** Source for [composition_indices_outer_degree]: the order
    sum_i alpha_i of the outer derivative is at most p,
    supporting the well-defined formula in Federer 3.1.11,
    p. 222. No derivatives above the available order are required. *)
Lemma composition_indices_outer_degree k p (a : composition_indices k p) :
  symmetric_multi_degree (composition_indices_unbound a)<=p.
Proof.
have hh := composition_multi_degree_le_weight (composition_indices_unbound a).
by rewrite composition_indices_weight in hh.
Qed.

(** Source for [composition_indices_complete]: every k-term
    nonnegative sequence of weight p occurs in the finite index
    type, supporting the exact summation set S(p) in Federer
    3.1.11, p. 222. *)
Theorem composition_indices_complete k p (a : symmetric_multi_index k) :
  composition_multi_weight a=p ->
  exists b : composition_indices k p, composition_indices_unbound b=a.
Proof.
move=>ha.
have hb i : a i<p.+1.
  rewrite ltnS -ha; exact: composition_multi_entry_le_weight.
pose f : {ffun 'I_k->'I_p.+1} := [ffun i=>Ordinal (hb i)].
have hw : (\sum_(i<k) (val i).+1*val (f i))==p.
  apply/eqP; rewrite /f; under eq_bigr do rewrite ffunE /=.
  exact ha.
exists (Sub f hw); apply/ffunP=>i.
by rewrite /composition_indices_unbound /f !ffunE.
Qed.

(** Source for [composition_indices_unbound_injective]: the finite
    representation counts each alpha exactly once, supporting the
    coefficient sum in Federer 3.1.11, p. 222. *)
Lemma composition_indices_unbound_injective k p :
  injective (@composition_indices_unbound k p).
Proof.
move=>a b hab; apply: val_inj; apply/ffunP=>i; apply: val_inj.
have hi := congr1 (fun z : symmetric_multi_index k=>z i) hab.
by move:hi; rewrite /composition_indices_unbound !ffunE.
Qed.

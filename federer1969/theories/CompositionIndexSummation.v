(** Federer (1969), 3.1.11, p. 222: regrouping the
    multinomial expansion by the weighted degree of a multiindex. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds
  CompositionMultiIndices FiniteRepresentationSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope nat_scope.

(** Source for [composition_expansion_indices]: the indices
    of the first double sum in the composition calculation,
    Federer 3.1.11, p. 222, including the constant term. *)
Definition composition_expansion_indices k :=
  {j : 'I_k.+1 & symmetric_indices k j}.

(** Source for [composition_expansion_unbound]: the exponent
    tuple underlying one term of the composition expansion,
    Federer 3.1.11, p. 222. *)
Definition composition_expansion_unbound k (a : composition_expansion_indices k) :
    symmetric_multi_index k := symmetric_indices_unbound (projT2 a).

(** Source for [composition_expansion_degree]: the outer degree
    of a term equals the sum of its exponents, supporting the
    regrouping in Federer 3.1.11, p. 222. *)
Lemma composition_expansion_degree k (a : composition_expansion_indices k) :
  symmetric_multi_degree (composition_expansion_unbound a)=val (projT1 a).
Proof. case:a=>j a; exact: symmetric_indices_unbound_degree. Qed.

(** Source for [composition_expansion_unbound_injective]: no
    exponent tuple occurs twice in the double sum, Federer
    3.1.11, p. 222. *)
Lemma composition_expansion_unbound_injective k :
  injective (@composition_expansion_unbound k).
Proof.
move=>[i a] [j b] he.
have hij : i = j.
  apply: val_inj.
  have hh := congr1 (@symmetric_multi_degree k) he.
  by rewrite !composition_expansion_degree in hh.
subst j; congr (existT _ i _).
apply: val_inj; apply/ffunP=>l; apply: val_inj.
have hh := congr1 (fun c : symmetric_multi_index k=>c l) he.
by move:hh; rewrite /composition_expansion_unbound /symmetric_indices_unbound !ffunE.
Qed.

(** Source for [composition_expansion_complete]: every tuple
    of total degree at most k occurs in the composition expansion,
    Federer 3.1.11, p. 222. *)
Lemma composition_expansion_complete k (a : symmetric_multi_index k) :
  symmetric_multi_degree a<=k ->
  exists b : composition_expansion_indices k, composition_expansion_unbound b=a.
Proof.
move=>ha.
have hj : symmetric_multi_degree a<k.+1 by rewrite ltnS.
pose j : 'I_k.+1 := Ordinal hj.
have hdeg : symmetric_multi_degree a==j by rewrite /j /= eqxx.
pose c : symmetric_degree_indices k j := Sub a hdeg.
exists (existT _ j (symmetric_indices_bound c)).
have hh := symmetric_indices_boundK c.
exact (congr1 (fun z : symmetric_degree_indices k j=>val z) hh).
Qed.

(** Source for [composition_expansion_weight_bound]: the
    weighted degree in the expansion is at most k squared,
    as in the last double sum of Federer 3.1.11, p. 222. *)
Lemma composition_expansion_weight_bound k (a : composition_expansion_indices k) :
  composition_multi_weight (composition_expansion_unbound a)<=k*k.
Proof.
apply: leq_trans (_ : composition_multi_weight (composition_expansion_unbound a)<=
  k*symmetric_multi_degree (composition_expansion_unbound a)) _.
- rewrite /composition_multi_weight /symmetric_multi_degree big_distrr /=.
  apply: leq_sum=>i _; apply: leq_mul=> //; exact: ltn_ord.
- rewrite composition_expansion_degree; apply: leq_mul=> //.
  by move:(ltn_ord (projT1 a)); rewrite ltnS.
Qed.

(** Source for [composition_expansion_weight_sum]: collecting
    the terms of weighted degree p gives exactly the printed
    set S(p), Federer 3.1.11, p. 222. The restriction p<=k
    ensures that no unavailable outer derivatives are introduced. *)
Lemma composition_expansion_weight_sum (V : zmodType) k p
    (F : symmetric_multi_index k->V) :
  p<=k ->
  (\sum_(a : composition_expansion_indices k |
      composition_multi_weight (composition_expansion_unbound a)==p)
      F (composition_expansion_unbound a)=
    \sum_(a : composition_indices k p) F (composition_indices_unbound a))%R.
Proof.
move=>hpk.
apply: (@finite_representation_sum (Finite.clone (composition_expansion_indices k) _)
  (Finite.clone (composition_indices k p) _) (Equality.clone (symmetric_multi_index k) _) V
  (@composition_expansion_unbound k) (@composition_indices_unbound k p)
  (fun a=>composition_multi_weight (composition_expansion_unbound a)==p) predT F).
- exact: composition_expansion_unbound_injective.
- exact: composition_indices_unbound_injective.
- move=>a /eqP ha; have [b hb] := composition_indices_complete ha.
  by exists b.
- move=>a _.
  have hh := leq_trans (composition_indices_outer_degree a) hpk.
  have [b hb] := composition_expansion_complete hh.
  exists b; split; last exact hb.
  by rewrite hb composition_indices_weight eqxx.
Qed.

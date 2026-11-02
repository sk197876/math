(** Federer (1969), 3.1.24, p. 239: isolate the
    unique composition term with outer order one before solving
    for the highest inner differential. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [composition_degree_one_support]: the unique
    degree-one term in S(p), supporting the inverse derivative
    formula in Federer 3.1.24, p. 239. One exponent
    is one, its position has weight p, and all others are zero. *)
Lemma composition_degree_one_support k p (a:composition_indices k p) :
  symmetric_multi_degree (composition_indices_unbound a)= 1 ->
  exists i:'I_k,(val i).+1=p /\
    composition_indices_unbound a i= 1 /\
    forall j,j!=i -> composition_indices_unbound a j=0.
Proof.
move=>hd.
pose alpha:=composition_indices_unbound a.
have hh:(\sum_(i<k) alpha i)== 1 by apply/eqP; exact hd.
move/sum_nat_eq1:hh=>[i [_ hi hz]].
have hzero j (hj:j!=i):alpha j=0:=hz j hj isT.
have hw:composition_multi_weight alpha=(val i).+1.
  rewrite /composition_multi_weight (bigD1 i) // hi muln1.
  have he:(\sum_(j<k | j!=i) (val j).+1*alpha j)=0.
    apply:big1=>j hj; by rewrite (hzero j hj) muln0.
  rewrite he.
  change ((val i).+1+0=(val i).+1); by rewrite addn0.
exists i; split; first by rewrite -hw composition_indices_weight.
by split.
Qed.

(** Source for [composition_degree_one_unique]: at a fixed
    weight there is at most one outer-linear composition term,
    supporting the separation of the inverse derivative in
    Federer 3.1.24, p. 239. *)
Lemma composition_degree_one_unique k p (a b:composition_indices k p) :
  symmetric_multi_degree (composition_indices_unbound a)= 1 ->
  symmetric_multi_degree (composition_indices_unbound b)= 1 -> a=b.
Proof.
move=>ha hb.
have [i [hi [hai hA]]]:=composition_degree_one_support ha.
have [j [hj [hbj hB]]]:=composition_degree_one_support hb.
have hij:i=j.
  apply:val_inj; exact (succn_inj (eq_trans hi (esym hj))).
rewrite -hij in hj hbj hB.
apply:composition_indices_unbound_injective; apply/ffunP=>q.
case hqi:(q==i).
- have he:q= i:=eqP hqi; by rewrite he hai hbj.
- have hq:q!=i by rewrite hqi.
  by rewrite (hA q hq) (hB q hq).
Qed.

(** Source for [composition_degree_one_exists]: the outer-
    linear term Dg composed with D^p f occurs in S(p),
    supporting the inverse calculation in Federer 3.1.24,
    p. 239. Its only exponent is one at the final
    position. Existence is proved using the complete finite
    representation of composition indices. *)
Lemma composition_degree_one_exists p :
  (1<=p)%N -> exists a:composition_indices p p,
    symmetric_multi_degree (composition_indices_unbound a)= 1.
Proof.
case:p=>[|p] hp; first by [].
pose alpha:symmetric_multi_index p.+1:=[ffun i=>if i==ord_max then 1 else 0].
have hw:composition_multi_weight alpha=p.+1.
  rewrite /composition_multi_weight (bigD1 ord_max) // /alpha ffunE eqxx muln1 /=.
  have hz:(\sum_(j<p.+1 | j!=ord_max) (val j).+1*(if j==ord_max then 1 else 0))=0.
    apply:big1=>j hj; by rewrite (negbTE hj) muln0.
  have he:(\sum_(j<p.+1 | j!=ord_max) (val j).+1*[ffun i:'I_p.+1=>if i==ord_max then 1 else 0] j)=0.
    under eq_bigr do rewrite ffunE.
    exact hz.
  rewrite he; change (p.+1+0=p.+1); by rewrite addn0.
have [a ha]:=composition_indices_complete hw.
exists a; rewrite ha /symmetric_multi_degree (bigD1 ord_max) // /alpha ffunE eqxx.
have hz:(\sum_(j<p.+1 | j!=ord_max) [ffun i:'I_p.+1=>if i==ord_max then 1 else 0] j)=0.
  apply:big1=>j hj; by rewrite ffunE (negbTE hj).
rewrite hz; change (1+0= 1); by rewrite addn0.
Qed.

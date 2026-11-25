(** Federer (1969), 3.1.24, pp. 239–240: the
    inverse-majorant recurrence bounds each inner monomial using
    only the already bounded lower derivative orders. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices CompositionRemainderIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_remainder_normalized_monomial_bound]:
    supporting the induction ||D^p f||<=lambda_p p! in
    Federer 3.1.24, pp. 239–240. In an outer-degree-
    greater-than-one term, every active inner order is below p.
    Bounds C_i<=lambda_i i! therefore bound its normalized
    monomial, without any assumption on the highest order. *)
Lemma inverse_remainder_normalized_monomial_bound (R:realType) k p
    (a:composition_indices k p) (C:'I_k->R) (lambda:nat->R) :
  (1<symmetric_multi_degree (composition_indices_unbound a))%N ->
  (forall i,0<=C i) -> (forall m,0<=lambda m) ->
  (forall i,((val i).+1<p)%N -> C i<=lambda (val i).+1*((val i).+1`!)%:R) ->
  symmetric_scalar_monomial (fun i:'I_k=>C i/((val i).+1`!)%:R) (composition_indices_unbound a)<=
    symmetric_scalar_monomial (fun i:'I_k=>lambda (val i).+1) (composition_indices_unbound a).
Proof.
move=>ha hC hL hLower.
rewrite /symmetric_scalar_monomial; apply:ler_prod=>i _; apply/andP; split.
- exact (exprn_ge0 _ (divr_ge0 (hC i) (ler0n _ _))).
- case he:(composition_indices_unbound a i)=>[|j]; first by rewrite !expr0.
  have hpos:(0<composition_indices_unbound a i)%N by rewrite he.
  have hi:=composition_remainder_uses_lower_orders ha hpos.
  have hfac:0<(((val i).+1`!)%:R:R) by rewrite ltr0n fact_gt0.
  have hRatio:C i/((val i).+1`!)%:R<=lambda (val i).+1.
    rewrite ler_pdivrMr //; exact (hLower i hi).
  exact (lerXn2r j.+1 (divr_ge0 (hC i) (ltW hfac)) (hL (val i).+1) hRatio).
Qed.

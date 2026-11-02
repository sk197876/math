(** Federer (1969), 2.10.43, printed p. 201: the finite prescribed-ball
    minimum has scale c<=1. Expand target and source weighted variances and
    use the pairwise nonexpansion inequality. This supporting algebraic
    lemma permits zero weights and repeated source points. Since every
    source point differs from the new anchor, the weighted squared-distance
    budget is strictly positive; no separate one-contact case is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import InnerProductUP InnerNorm InnerWeightedVariance PositiveWeightedBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [kirszbraun_weighted_contact_scale_le_one]: direct final c<=1
    estimate in the finite-ball argument of 2.10.43, p. 201 Both inner
    products are abstract; dimension is unnecessary once the finite contact
    representation and its weighted mean have been supplied. *)
Theorem kirszbraun_weighted_contact_scale_le_one (R : realType)
    (U V : lmodType R) (B : U -> U -> R) (C : V -> V -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) (I : finType)
    (u : I -> U) (v : I -> V) (w : I -> R) (a : U) (b : V) (c : R) :
  0<=c -> (forall i, 0<=w i) -> (\sum_i w i= 1) ->
  (\sum_i w i*:(v i-b)=0) ->
  (forall i, inner_norm hC (v i-b)=c*inner_norm hB (u i-a)) ->
  (forall i j, inner_norm hC (v i-v j)<=inner_norm hB (u i-u j)) ->
  (forall i, u i!=a) -> c<=1.
Proof.
move=> hc hw hsum hmean hcontact hLip hne.
pose x i := u i-a.
pose y i := v i-b.
pose S := \sum_i w i*inner_norm hB (x i)^+2.
have hS : 0<S.
  apply: (@finite_positive_weighted_budget R I w (fun i=>inner_norm hB (x i)^+2) hw hsum).
  move=> i; have hx : 0<inner_norm hB (x i) by rewrite /x inner_norm_gt0 subr_eq0.
  by rewrite exprn_gt0.
have htarget : (\sum_i w i*inner_norm hC (y i)^+2)=c^+2*S.
  rewrite /S mulr_sumr; apply: eq_bigr=> i _.
  rewrite /y /x (hcontact i) exprMn; ring.
have hymean : \sum_i w i*:y i=0 := hmean.
have hyvar := @inner_weighted_variance_identity R V C hC I y w hsum.
rewrite hymean inner_norm0 expr0n mulr0 subr0 htarget in hyvar.
have hxvar := @inner_weighted_variance_identity R U B hB I x w hsum.
have hsource : (\sum_i \sum_j (w i*w j)*inner_norm hB (x i-x j)^+2)<=2*S.
  rewrite hxvar.
  have hh := sqr_ge0 (inner_norm hB (\sum_i w i*:x i)).
  change (is_true (2*S-2*inner_norm hB (\sum_i w i*:x i)^+2<=2*S)); nra.
have hcompare : (\sum_i \sum_j (w i*w j)*inner_norm hC (y i-y j)^+2)<=
    \sum_i \sum_j (w i*w j)*inner_norm hB (x i-x j)^+2.
  apply: ler_sum=> i _; apply: ler_sum=> j _.
  have hey : y i-y j=v i-v j by rewrite /y opprB addrA subrK.
  have hex : x i-x j=u i-u j by rewrite /x opprB addrA subrK.
  have hsq : inner_norm hC (y i-y j)^+2<=inner_norm hB (x i-x j)^+2.
    rewrite (ler_sqr (inner_norm_nonnegative hC _) (inner_norm_nonnegative hB _)) hey hex.
    exact: hLip.
  exact (ler_wpM2l (mulr_ge0 (hw i) (hw j)) hsq).
have hbound := le_trans hcompare hsource.
rewrite hyvar in hbound.
have htwoS : 0<2*S by rewrite mulr_gt0 // ltr0n.
have hsq : c^+2<=1.
  rewrite -(ler_pM2r htwoS) mul1r.
  nra.
nra.
Qed.

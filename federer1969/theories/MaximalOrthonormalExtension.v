(** Federer (1969), 1.7.3, p. 29: supporting induction for the successive
    maximisation construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies InfiniteSequence MaximalOrthonormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Extension.
Variable R : rcfType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable k : nat.
Variable e : 'I_k -> V.
Hypothesis he : is_maximal_orthonormal_family S hB e.
Variable v : V.
Hypothesis hv : inner_norm hB v = 1.
Hypothesis ho : forall i, B v (e i) = 0.
Hypothesis hmax : forall x, inner_norm hB x = 1 ->
  (forall i, B x (e i) = 0) -> S x x <= S v v.

(** Source for [maximal_orthonormal_snoc]: Federer 1.7.3,
    p. 29, appending a maximiser on the next constrained unit
    sphere preserves every preceding maximisation property. *)
Theorem maximal_orthonormal_snoc :
  is_maximal_orthonormal_family S hB (ordinal_snoc e v).
Proof.
constructor.
- apply: (@orthonormal_snoc R V B hB k e v
    (maximal_family_orthonormal he)) => //.
  by rewrite -(inner_norm_sqr hB v) hv expr1n.
- move=> i x hx; case: (unliftP ord_max i) => [j ->|->] hpre.
  + rewrite ordinal_snoc_lift; apply: (maximal_family_value he hx).
    move=> a haj.
    have hlt : (lift ord_max a < lift ord_max j)%N by rewrite !lift_max.
    have hh := hpre (lift ord_max a) hlt.
    by rewrite ordinal_snoc_lift in hh.
  + rewrite ordinal_snoc_last; apply: hmax hx _ => j.
    have hlt : (lift ord_max j < (ord_max : 'I_k.+1))%N by rewrite lift_max; exact: ltn_ord.
    have hh := hpre (lift ord_max j) hlt.
    by rewrite ordinal_snoc_lift in hh.
Qed.
End Extension.

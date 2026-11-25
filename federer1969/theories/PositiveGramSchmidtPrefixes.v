(** Federer (1969), 3.2.47, p. 282: finite-prefix bookkeeping
    for the actual positive Gram–Schmidt recurrence. These supporting
    equations precede existence and the sealed local-section object. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP OrthonormalProjection InnerNormalization
  FinitePrefixes InfiniteSequence PositiveGramSchmidtUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_residual_before]: retaining
    each earlier residual when adjoining a last vector, supporting
    the finite recurrence in 3.2.47, p. 282. *)
Lemma positive_gram_schmidt_residual_before (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n.+1->V) (v:'I_n->V) w (i:'I_n):
  positive_gram_schmidt_residual hB u (ordinal_snoc v w)
      (widen_ord (leqnSn n) i)=
    positive_gram_schmidt_residual hB (family_prefix (leqnSn n) u) v i.
Proof.
pose j:=widen_ord (leqnSn n) i.
have hPrefix:family_prefix (ltnW (ltn_ord j)) (ordinal_snoc v w)=
    family_prefix (ltnW (ltn_ord i)) v.
  apply:funext=>k.
  exact (@family_prefix_snoc V (val i) n (ltnW (ltn_ord i))
    (ltnW (ltn_ord j)) v w k).
by rewrite /positive_gram_schmidt_residual -/j hPrefix.
Qed.

(** Source for [positive_gram_schmidt_residual_last]: the new
    last residual uses exactly the preceding orthonormal family,
    supporting the induction in 3.2.47, p. 282. *)
Lemma positive_gram_schmidt_residual_last (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n.+1->V) (v:'I_n->V) w:
  positive_gram_schmidt_residual hB u (ordinal_snoc v w) ord_max=
    u ord_max-orthonormal_projection hB v (u ord_max).
Proof.
have hPrefix:family_prefix (ltnW (ltn_ord (ord_max:'I_n.+1)))
    (ordinal_snoc v w)=v.
  apply:funext=>i.
  rewrite (@family_prefix_snoc V n n (leqnn n)
    (ltnW (ltn_ord (ord_max:'I_n.+1))) v w i).
  exact:family_prefix_refl.
by rewrite /positive_gram_schmidt_residual hPrefix.
Qed.

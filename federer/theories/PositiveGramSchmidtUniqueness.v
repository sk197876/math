(** Federer (1969), 3.2.47, p. 282: positive residual
    normalization determines the section's ordered orthonormal family.
    Uniqueness permits an opaque choice without arbitrary signs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerNormalization OrthonormalProjection
  FinitePrefixes PositiveGramSchmidtUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_unique]: uniqueness of the
    exact finite normalized recurrence used in 3.2.47, p. 282.
    No continuity of a choice operation or of the earlier
    arbitrary-sign orthonormalisation is assumed. *)
Theorem positive_gram_schmidt_unique (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u v w:'I_n->V):
  is_positive_gram_schmidt hB u v ->is_positive_gram_schmidt hB u w ->v=1 w.
Proof.
move=>hv hw.
have hPrefix:forall k (i:'I_n),(val i<k)%N ->v i=w i.
  elim=>[|k ih] i hi; first by rewrite ltn0 in hi.
  case:(ltnP (val i) k)=>hik; first exact:ih i hik.
  have hikEq:val i=k by apply/eqP; rewrite eqn_leq hik -ltnS hi.
  rewrite (positive_gram_schmidt_equation hv i)
    (positive_gram_schmidt_equation hw i).
  have hPrevious:family_prefix (ltnW (ltn_ord i)) v=
      family_prefix (ltnW (ltn_ord i)) w.
    apply:funext=>j; apply:ih.
    change ((val j<k)%N); by rewrite -hikEq; exact:ltn_ord.
  by rewrite /positive_gram_schmidt_residual hPrevious.
move=>i; exact:hPrefix n i (ltn_ord i).
Qed.

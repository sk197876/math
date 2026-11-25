(** Federer (1969), 4.1.27, p. 384:
    affine independence of the original vertices
    makes normalized barycentric coefficients unique.
    Reuse the earlier finite independence of
    u_i-u_0; the finite empty family includes
    the single zero-dimensional vertex. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  FiniteIndependence CurrentSimplexFrame.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_normalized_barycentric_translation]: translating
    by u_0 converts normalized barycentric sums
    to the earlier edge family of
    4.1.11, p. 366, supporting injectivity in
    4.1.27, p. 384. Coefficients need not
    be positive for this identity. *)
Lemma simplex_normalized_barycentric_translation (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (t:'I_(m.+1)->R):
  (\sum_i t i)= 1->
  (\sum_i t i*:v i)=v ord0+
    \sum_(i:'I_m) t (lift ord0 i)*:current_simplex_edge_family v i.
Proof.
move=>hSum.
have hTranslate:(\sum_i t i*:(v i-v ord0))=(\sum_i t i*:v i)-v ord0.
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml hSum scale1r.
rewrite big_ord_recl /= subrr scaler0 add0r in hTranslate.
by rewrite /current_simplex_edge_family hTranslate addrC subrK.
Qed.

(** Source for [simplex_nondegenerate_barycentric_unique]: the
    independence condition in the injectivity clause
    of 4.1.27, p. 384, identifies every
    normalized coefficient of the original vertices.
    This is the finite independence law
    already proved in Chapter 1. *)
Theorem simplex_nondegenerate_barycentric_unique (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (t s:'I_(m.+1)->R):
  is_nondegenerate_current_simplex v->
  (\sum_i t i)= 1->(\sum_i s i)= 1->
  (\sum_i t i*:v i)=(\sum_i s i*:v i)->t=s.
Proof.
move=>hIndependent hT hS hImages.
rewrite (simplex_normalized_barycentric_translation v hT)
  (simplex_normalized_barycentric_translation v hS) in hImages.
have hTail:(\sum_(i:'I_m) t (lift ord0 i)*:current_simplex_edge_family v i)=
    \sum_(i:'I_m) s (lift ord0 i)*:current_simplex_edge_family v i.
  exact:addrI hImages.
have hZero:(\sum_(i:'I_m) (t (lift ord0 i)-s (lift ord0 i))*:
    current_simplex_edge_family v i)=0.
  under eq_bigr do rewrite scalerBl.
  by rewrite sumrB hTail subrr.
have hTailCoefficients:forall i:'I_m,t (lift ord0 i)=s (lift ord0 i).
  move=>i;exact:subr0_eq (@hIndependent
    (fun i=>t (lift ord0 i)-s (lift ord0 i)) hZero i).
have hTailSum:(\sum_(i:'I_m) t (lift ord0 i))=
    \sum_(i:'I_m) s (lift ord0 i).
  apply:eq_bigr=>i _;exact:hTailCoefficients.
have hFirst:t ord0=s ord0.
  have hTotal:=eq_trans hT (esym hS).
  rewrite !big_ord_recl /= hTailSum in hTotal.
  exact:addIr hTotal.
apply:funext=>i;case:(unliftP ord0 i)=>[j ->|->].
- exact:hTailCoefficients.
- exact:hFirst.
Qed.

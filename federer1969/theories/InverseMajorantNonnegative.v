(** Federer (1969), 3.1.24, pp. 239–240: the
    majorant recurrence has nonnegative coefficients and depends
    only on earlier positive orders. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices CompositionRemainderIndices InverseMajorantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_majorant_sequence_nonnegative]: the
    nonnegative lambda_p used to bound inverse derivatives in
    Federer 3.1.24, pp. 239–240. This is proved
    from the defining recurrence and positive beta,gamma; it
    is not an extra specification hypothesis. *)
Theorem inverse_majorant_sequence_nonnegative (R:realType) (b g:R) (lambda:nat->R) :
  0<b -> 0<g -> is_inverse_majorant_sequence b g lambda -> forall p,0<=lambda p.
Proof.
move=>hb hg [hz [h1 hrec]].
have hbase:0<=lambda 1%N by rewrite h1 invr_ge0; exact (mulr_ge0 (ltW hb) (ltW hg)).
elim/ltn_ind=>p ih.
case:p ih=>[|p] ih; first by rewrite hz.
case:p ih=>[|p] ih; first exact hbase.
rewrite hrec // /inverse_majorant_remainder.
apply:mulr_ge0; first exact hbase.
apply:sumr_ge0=>a ha.
apply:mulr_ge0.
- apply:divr_ge0; last exact:ler0n.
  exact (mulr_ge0 (exprn_ge0 _ (ltW hg)) (ler0n _ _)).
- apply:prodr_ge0=>i _.
  case he:(composition_indices_unbound a i)=>[|j]; first by rewrite expr0 ler01.
  have hpos:(0<composition_indices_unbound a i)%N by rewrite he.
  have hi:=composition_remainder_uses_lower_orders ha hpos.
  exact (exprn_ge0 j.+1 (ih (val i).+1 hi)).
Qed.

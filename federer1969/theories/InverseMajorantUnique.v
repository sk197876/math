(** Federer (1969), 3.1.24, pp. 239–240: the
    lower-order recurrence uniquely determines the inverse
    majorant sequence. This supports using a proved scalar
    witness through an abstract sealed interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SymmetricMultiIndices CompositionMultiIndices CompositionRemainderIndices
  SymmetricDividedMonomials InverseMajorantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_majorant_sequence_unique]: the
    inductive definition in Federer 3.1.24, pp. 239–240,
    determines one sequence. Every positive exponent in T(p)
    refers to an order strictly below p, as proved from
    the weighted and ordinary degree equations. *)
Theorem inverse_majorant_sequence_unique (R:realType) (b g:R) (lambda mu:nat->R) :
  is_inverse_majorant_sequence b g lambda -> is_inverse_majorant_sequence b g mu ->
  forall p,lambda p=mu p.
Proof.
move=>[hL0 [hL1 hL]] [hM0 [hM1 hM]].
elim/ltn_ind=>p ih.
case:p ih=>[|p] ih; first by rewrite hL0 hM0.
case:p ih=>[|p] ih; first by rewrite hL1 hM1.
rewrite hL // hM // hL1 hM1; congr (_*_).
rewrite /inverse_majorant_remainder; apply:eq_bigr=>a ha.
congr (_*_); apply:eq_bigr=>i _.
case he:(composition_indices_unbound a i)=>[|j]; first by rewrite !expr0.
have hpos:(0<composition_indices_unbound a i)%N by rewrite he.
have hi:=composition_remainder_uses_lower_orders ha hpos.
by rewrite (ih (val i).+1 hi).
Qed.

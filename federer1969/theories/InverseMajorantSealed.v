(** Federer (1969), 3.1.24, pp. 239–240: the
    inverse-majorant sequence is exposed only through its proved
    recurrence and exponential bound. The scalar quadratic witness
    is hidden by opaque module ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InverseMajorantUP InverseMajorantConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type INVERSE_MAJORANT.
  (** Source for [sequence]: the sequence lambda_1,lambda_2,...
      defined in Federer 3.1.24, pp. 239–240, with
      its auxiliary order-zero convention. This signature field
      must be implemented together with the laws below. *)
  Parameter sequence:forall (R:realType) (b g:R),0<b -> 0<g -> nat->R.
  (** Source for [laws]: the defining initial value and
      lower-order recurrence in Federer 3.1.24, pp. 239–240.
      The implementation proves this field from existence. *)
  Parameter laws:forall (R:realType) (b g:R) (hb:0<b) (hg:0<g),
    is_inverse_majorant_sequence b g (@sequence R b g hb hg).
  (** Source for [exponential_bound]: the finite exponential
      majorant for lambda_p in Federer 3.1.24, p. 240.
      The implementation proves this field using the analytic
      scalar quadratic inverse. *)
  Parameter exponential_bound:forall (R:realType) (b g:R) (hb:0<b) (hg:0<g),
    exists C:R,0<C /\ forall p,(1<=p)%N -> @sequence R b g hb hg p<=C^+p.
End INVERSE_MAJORANT.

Module InverseMajorant : INVERSE_MAJORANT.
  (** Source for [sequence]: choose a witness to the proved
      existence assertion supporting Federer 3.1.24, p. 240.
      The choice is hidden by the module signature. *)
  Definition sequence (R:realType) (b g:R) (hb:0<b) (hg:0<g):nat->R :=
    projT1 (cid (@inverse_majorant_sequence_exists R b g hb hg)).
  (** Source for [laws]: the defining recurrence from the
      proved scalar witness, Federer 3.1.24, pp. 239–240. *)
  Lemma laws (R:realType) (b g:R) (hb:0<b) (hg:0<g) :
    is_inverse_majorant_sequence b g (@sequence R b g hb hg).
  Proof. exact (projT2 (cid (@inverse_majorant_sequence_exists R b g hb hg))).1. Qed.
  (** Source for [exponential_bound]: the proved scalar witness
      has a positive finite exponential bound, Federer 3.1.24,
      p. 240. Downstream inverse proofs use this law
      without importing the quadratic construction. *)
  Lemma exponential_bound (R:realType) (b g:R) (hb:0<b) (hg:0<g) :
    exists C:R,0<C /\ forall p,(1<=p)%N -> @sequence R b g hb hg p<=C^+p.
  Proof. exact (projT2 (cid (@inverse_majorant_sequence_exists R b g hb hg))).2. Qed.
End InverseMajorant.

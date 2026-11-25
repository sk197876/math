(** Federer (1969), 4.1.6, pp. 353–355:
    a one-form field whose actual first differential
    is symmetric is closed. This is the original
    two-coordinate cancellation used for pulled-back
    coordinate differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Alternating OneFormLinear ExteriorDifferentialUP ExteriorDifferentialNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_one_form_exterior_value_zero]:
    the original signed two-term formula vanishes
    for a symmetric first derivative,
    Federer 4.1.6, pp. 353–355. *)
Theorem symmetric_one_form_exterior_value_zero (K:fieldType) (V W:lmodType K)
    (L:Hom V (A_m V W 1)):
  (forall u v,one_hom (L u) v=one_hom (L v) u)->
  is_exterior_differential_value L (0:A_m V W 2).
Proof.
move=>hSym t; rewrite form_zeroE exterior_differential_trace_tuple_values.
have hO0:exterior_omitted_tuple t (ord0:'I_2)=
    [tuple tnth t (lift (ord0:'I_2) (ord0:'I_1))].
  apply:eq_from_tnth=>i; rewrite (ord1 i) /exterior_omitted_tuple tnth_mktuple.
  by [].
have hO1:exterior_omitted_tuple t (lift (ord0:'I_2) (ord0:'I_1))=[tuple tnth t (ord0:'I_2)].
  apply:eq_from_tnth=>i; rewrite (ord1 i) /exterior_omitted_tuple tnth_mktuple.
  change (tnth t (lift (lift (ord0:'I_2) (ord0:'I_1)) (ord0:'I_1))=tnth t (ord0:'I_2)).
  congr (tnth t _); by apply:val_inj.
rewrite big_ord_recl big_ord1 expr0 expr1 scale1r scaleN1r.
rewrite hO0 hO1.
change (0=one_hom (L (tnth t (ord0:'I_2))) (tnth t (lift (ord0:'I_2) (ord0:'I_1)))-
  one_hom (L (tnth t (lift (ord0:'I_2) (ord0:'I_1)))) (tnth t (ord0:'I_2))).
by rewrite hSym subrr.
Qed.

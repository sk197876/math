(** Federer (1969), 4.1.6, pp. 352–353: linearity
    of the original signed exterior-differential formula.
    These consequences use its independent tuple laws
    and the existing exterior pairing alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom AlternatingForms AlternatingPairing ExteriorDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_differential_trace_linear]: each
    original defining tuple evaluation is linear in
    the first differential, Federer 4.1.6,
    pp. 352–353. *)
Lemma exterior_differential_trace_linear (K:fieldType) (V W:lmodType K) m
    (t:m.+1.-tuple V):linear (fun L:Hom V (A_m V W m)=>exterior_differential_trace L t).
Proof.
move=>c L M; rewrite /exterior_differential_trace.
have hTerm i:pairing (exterior_signed_omission t i) ((c*:L+M) (tnth t i))=
    c*:pairing (exterior_signed_omission t i) (L (tnth t i))+
      pairing (exterior_signed_omission t i) (M (tnth t i)).
  by rewrite hom_addE hom_scaleE ((@pairing_bilinear K V W m).2).
under eq_bigr do rewrite hTerm.
by rewrite big_split scaler_sumr.
Qed.

(** Source for [exterior_differential_linear_values]: the
    original exterior differentiation commutes with
    linear combinations, Federer 4.1.6, p. 353. *)
Theorem exterior_differential_linear_values (K:fieldType) (V W:lmodType K) m c
    (L M:Hom V (A_m V W m)) (a b:A_m V W m.+1):
  is_exterior_differential_value L a ->is_exterior_differential_value M b ->
  is_exterior_differential_value (c*:L+M) (c*:a+b).
Proof.
move=>ha hb t; rewrite form_addE form_scaleE ha hb.
exact:esym (@exterior_differential_trace_linear K V W m t c L M).
Qed.

(** Federer (1969), 3.3.4, p. 291:
    the finite positive real coefficient bounds
    for replacing reference ball masses by r^m.
    Their proofs use positive denominators only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_radius_power_upper]:
    supporting the zero-limit comparison in Federer
    3.3.4, p. 291. A reference mass bounded
    above by K r^m has normalized mass at
    most K at every actual positive radius. *)
Lemma structure_radius_power_upper (R:realType) m (b r K:R):
  0<r ->b<=K*r^+m ->b*(r^-1)^+m<=K.
Proof.
move=>hr hBound; rewrite exprVn.
by rewrite (ler_pdivrMr _ _ (exprn_gt0 m hr)).
Qed.

(** Source for [structure_radius_power_inverse_lower]:
    supporting passage from closed r-balls to
    open 2r-balls in Federer 3.3.4, p. 291.
    The inverse reference mass is bounded by
    2^m/a times the actual (2r)^(-m) weight.
    The degree-zero normalization remains positive. *)
Lemma structure_radius_power_inverse_lower (R:realType) m (b r a:R):
  0<r ->0<a ->a*r^+m<=b ->
  b^-1<=((2:R)^+m/a)*((2*r)^-1)^+m.
Proof.
move=>hr ha hBound.
have hDen:0<a*r^+m by rewrite mulr_gt0 // exprn_gt0.
have hb:0<b:=lt_le_trans hDen hBound.
have hInv:b^-1<=(a*r^+m)^-1.
  by rewrite lef_pV2 ?posrE.
have hCancel:((2:R)^+m/a)*((2*r)^-1)^+m=(a*r^+m)^-1.
  rewrite exprVn exprMn invfM.
  field; by rewrite ?pnatr_eq0 ?expf_neq0 ?gt_eqF.
by rewrite hCancel.
Qed.

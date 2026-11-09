(** Federer (1969), 3.3.18, p. 301: normalize the strict
    cone inequality without changing its original aperture. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cone_angle_unit_normalization]: the passage to
    unit directions in the last paragraph of Federer 3.3.18,
    p. 301. Positive dilation preserves the original strict
    aperture inequality. Both scale factors are genuinely positive. *)
Lemma cone_angle_unit_normalization (R:realType) (s t d:R):
  0<s ->0<t ->s^-1*d<t ->t^-1*d<s.
Proof.
move=>hs ht hAngle.
have hFirst:s*(s^-1*d)<s*t by rewrite ltr_pM2l.
rewrite mulrA mulfV ?gt_eqF // mul1r in hFirst.
by rewrite [t^-1*d]mulrC ltr_pdivrMr.
Qed.

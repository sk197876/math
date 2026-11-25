(** Federer (1969), 3.3.19, p. 305: the acute
    angle with prescribed positive aperture. All scalar
    choices are local and use the sealed circular laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularScalarLipschitz CircularTrigonometryUP CircularTrigonometrySealed
  CircularCosineReflection CircularSineOrder CircularSineChordBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Acute.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_acute_sine_parameter_exists]: the
    local angle 0<alpha<pi/2 with sin(alpha)= s,
    0<s<1, of 3.3.19, p. 305. Its cosine is
    positive and alpha>=s, as used in the density bound. *)
Theorem circular_acute_sine_parameter_exists (s:R):
  0<s ->s<1 ->exists a:R,0<a /\a<p/2 /\S a= s /\0<C a /\s<=a.
Proof.
move=>hs hs1.
pose D:= @CircularTrigonometry.arccosine R.
have hp:= real_trigonometry_pi_positive hb.
have hsLower:-1<=s by lra.
have hsUpper:s<=1:= ltW hs1.
have [hD0 hDP]:= @circular_trig_acos_range R S C (@CircularTrigonometry.arcsine R) D p ht s hsLower hsUpper.
have hCos:= @circular_trig_acos_cosine R S C (@CircularTrigonometry.arcsine R) D p ht s hsLower hsUpper.
have hDNonzero:D s!=0.
  apply/eqP=>hZero.
  rewrite hZero (real_cosine_zero hb) in hCos;lra.
have hDPositive:0<D s by rewrite lt_neqAle eq_sym hDNonzero hD0.
have hDHalf:D s<p/2.
  rewrite ltNge;apply/negP=>hBad.
  have hHalf0:0<=p/2 by lra.
  have hC:=@circular_cosine_weak_decrease R (p/2) (D s) hHalf0 hBad hDP.
  rewrite circular_cosine_quarter_turn hCos in hC;lra.
pose a:= p/2-D s.
have ha:0<a by rewrite /a;lra.
have haP:a<p/2 by rewrite /a;lra.
have hSa:S a= s.
  have hAngle:p/2-(p/2-D s)= D s by ring.
  have hReflection:=@circular_sine_reflected_cosine R a.
  rewrite /a hAngle hCos in hReflection.
  exact:esym hReflection.
have hCa:0<C a.
  have ha0:0<=a:= ltW ha.
  have haPi:a<=p by lra.
  have hHalf0:0<=p/2 by lra.
  have hHalfPi:p/2<=p by lra.
  have hStrict:= @circular_trig_cosine_decreases R S C (@CircularTrigonometry.arcsine R) D p ht
    a (p/2) ha0 haPi hHalf0 hHalfPi haP.
  by rewrite circular_cosine_quarter_turn in hStrict.
have hSBound:S a<=a.
  have h:= @circular_sine_nonexpanding R a 0.
  rewrite hSa (real_sine_zero hb) !subr0 (ger0_norm (ltW ha))
    (ger0_norm (ltW hs)) in h.
  by rewrite hSa.
exists a;split=>//;split=>//;split=>//;split=>//.
by rewrite -hSa.
Qed.
End Acute.

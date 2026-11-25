(** Federer (1969), 3.3.19, p. 305: local
    auxiliary apertures and cap errors approach the exact
    printed conical density constant without changing the cone. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularAcuteSineParameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Parameters.
Variable R:realType.
Local Notation pi:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).

(** Source for [circular_conical_density_parameters]: for
    any original 0<s<1 and positive target k<1/(2pi),
    local acute alpha, small beta and positive error eps
    give ((alpha-beta)/pi-2eps)/(2s)>k, with
    sin(alpha)<s. This makes both cone inequalities
    strict and recovers the exact density bound in
    3.3.19, p. 305 by order approximation. *)
Theorem circular_conical_density_parameters (s k:R):
  0<s ->s<1 ->0<k ->k<1/(2* pi) ->
  exists alpha beta eps:R,
    0<alpha /\alpha<pi/2 /\0<S alpha /\S alpha<s /\
    0<beta /\beta<=pi /\0<eps /\
    k<((alpha-beta)/pi-2* eps)/(2* s).
Proof.
move=>hs hs1 hk hkBound.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hDen:0<2* pi by lra.
have hDenN:2* pi!=0 by rewrite gt_eqF.
have hK:2* pi* k<1.
  have h:2* pi* k<2* pi*(1/(2* pi)) by rewrite ltr_pM2l.
  by rewrite div1r mulfV // in h.
pose sigma:= s*(1+2* pi* k)/2.
have hKPositive:0<2*pi*k by rewrite mulr_gt0.
have hFactor:0<1+2*pi*k by lra.
have hSigma:0<sigma by rewrite /sigma divr_gt0 // mulr_gt0.
have hProduct:s*(1+2*pi*k)<s*2.
  rewrite ltr_pM2l //;lra.
have hSigmaS:sigma<s by rewrite /sigma ltr_pdivrMr //.
have hSigma1:sigma<1:= lt_trans hSigmaS hs1.
pose m:= sigma-2* pi* s* k.
have hMargin:m=s*(1-2*pi*k)/2 by rewrite /m /sigma;field.
have hRemaining:0<1-2*pi*k by lra.
have hm:0<m by rewrite hMargin divr_gt0 // mulr_gt0.
pose beta:= Num.min (pi/4) (m/4).
have hPiQuarter:0<pi/4 by lra.
have hMQuarter:0<m/4 by lra.
have hBeta:0<beta by rewrite /beta lt_min hPiQuarter hMQuarter.
have hBetaPi:beta<=pi.
  have h:beta<=pi/4 by rewrite /beta ge_min lexx.
  lra.
have hBetaM:beta<=m/4 by rewrite /beta ge_min lexx orbT.
pose eps:= m/(8* pi).
have hDenE:0<8* pi by lra.
have hEps:0<eps by rewrite /eps divr_gt0.
have hPiN:pi!=0 by rewrite gt_eqF.
have hBudget:2* eps* pi= m/4.
  rewrite /eps;field;by rewrite hPiN.
have [alpha [hAlpha [hAlphaHalf [hSine [hCos hAlphaLower]]]]]:=
  @circular_acute_sine_parameter_exists R sigma hSigma hSigma1.
have hGoal:k<((alpha-beta)/pi-2* eps)/(2* s).
  have hSden:0<2* s by lra.
  rewrite ltr_pdivlMr //.
  have hScalar:(alpha-beta)/pi-2* eps=(alpha-beta-2* eps* pi)/pi by field.
  rewrite hScalar ltr_pdivlMr //.
  rewrite /m in hm hBetaM hBudget;nra.
exists alpha,beta,eps;split=>//;split=>//;split;first by rewrite hSine.
split;first by rewrite hSine.
by split=>//;split=>//;split.
Qed.
End Parameters.

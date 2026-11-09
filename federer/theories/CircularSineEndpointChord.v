(** Federer (1969), 3.3.19, p. 302: stronger
    local scalar chord bounds for the original halfplane
    count. The only inputs are proved scalar circular laws;
    no geometric counting conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineChordBound CircularSineOrder StrictMidpointChordPositive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Chord.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_endpoint_chord]: the actual
    scalar sine lies strictly above every endpoint chord
    in the first quadrant, supporting the halfplane count
    in 3.3.19, p. 302. The same compact-minimum
    argument as the printed sine estimate applies. *)
Theorem circular_sine_endpoint_chord L x:
  0<L ->L<=p/2 ->0<x ->x<L ->(S L/L)* x<S x.
Proof.
move=>hL hLp hx hxL.
have hLN:L!= 0 by rewrite gt_eqF.
pose F:R^o->R^o:=fun t=>S t-(S L/L)* t.
have hLinear:continuous (fun t:R^o=>((S L/L)* t:R^o)).
  have hIdentity:continuous (fun t:R^o=>t) by move=>t U hU.
  have hConstant:continuous (fun _:R^o=>(S L/L:R^o)) by exact:cst_continuous.
  move=>t;exact (@continuousM R [the topologicalType of R^o]
    (fun _:R^o=>(S L/L:R^o)) (fun t:R^o=>t) t (hConstant t) (hIdentity t)).
have hF:continuous F.
  move=>t;exact (@continuousB R [the normedModType R of R^o]
    [the topologicalType of R^o] (S:R^o->R^o) (fun t:R^o=>((S L/L)* t:R^o)) t
    (@circular_sine_continuous R t) (hLinear t)).
have hF0:F 0= 0 by rewrite /F (real_sine_zero hb) mulr0 subrr.
have hFEnd:F L= 0 by rewrite /F divfK // subrr.
have hMid u v:0<=u ->u<v ->v<=L ->(F u+F v)/2<F ((u+v)/2).
  move=>hu huv hv.
  have hvp:v<=p/2:=le_trans hv hLp.
  have hS:=@circular_sine_strict_midpoint R u v hu huv hvp.
  rewrite /F.
  have hEq:(S u-(S L/L)* u+(S v-(S L/L)* v))/2=
      (S u+S v)/2-(S L/L)*((u+v)/2) by ring.
  by rewrite hEq ltrD2r.
have hPositive:=@strict_midpoint_chord_positive R F L hL hF hF0 hFEnd hMid x hx hxL.
by move:hPositive;rewrite /F subr_gt0.
Qed.

(** Source for [circular_sine_half_step_strict]: the
    half-step sine exceeds 1/(n-1) for every original
    subdivision n>= 4, supporting the halfplane count in
    3.3.19, p. 302. Closed boundary contacts are
    retained through the strict estimate. *)
Lemma circular_sine_half_step_strict n:(4<=n)%N ->
  (n%:R-1)^-1<S (p/(2* n%:R)).
Proof.
move=>hn.
have hp:=real_trigonometry_pi_positive hb.
have hpN:p!= 0 by rewrite gt_eqF.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hD:(0<2* n%:R:>R) by nra.
have hDN:(2* n%:R:R)!= 0 by rewrite gt_eqF.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hNCancel:(n%:R:R)* n%:R^-1= 1 by rewrite mulfV.
have hQuarter:(4* n%:R^-1<= 1:>R).
  have hh:=ler_wpM2r (ltW hInv) hN4;by rewrite hNCancel in hh.
have hL:0<p/6 by rewrite divr_gt0 ?ltr0n.
have hLp:p/6<=p/2 by lra.
have hx:0<p/(2* n%:R) by rewrite divr_gt0.
have hRewrite:p/(2* n%:R)=(p/2)* n%:R^-1 by rewrite invfM;ring.
have hxL:p/(2* n%:R)<p/6 by rewrite hRewrite;nra.
have hChord:=@circular_sine_endpoint_chord (p/6) (p/(2* n%:R)) hL hLp hx hxL.
rewrite (@circular_sine_twelfth_turn R) in hChord.
have hScalar:((1/2)/(p/6))*(p/(2* n%:R))=(3/2)* n%:R^-1.
  have hInverseAngle:(p/6)^-1= 6* p^-1 by rewrite invf_div.
  have hInverseDenominator:(2* n%:R:R)^-1=(1/2)* n%:R^-1 by rewrite invfM;ring.
  rewrite hInverseAngle hInverseDenominator.
  have hRearrange:(1/2)*(6* p^-1)*(p*((1/2)* n%:R^-1))=
      (3/2)* n%:R^-1*(p* p^-1) by nra.
  by rewrite hRearrange mulfV // mulr1.
rewrite hScalar in hChord.
have hNm1:(0<n%:R-1:>R) by lra.
have hNm1N:(n%:R-1:R)!= 0 by rewrite gt_eqF.
have hInverse:(0<(n%:R-1)^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R-1:R)*(n%:R-1)^-1= 1 by rewrite mulfV.
have hScaled:=congr1 (fun z:R=>n%:R^-1* z) hCancel.
have hRelation:((n%:R:R)-1)^-1-n%:R^-1*(n%:R-1)^-1=n%:R^-1.
  have hAlgebra:(n%:R:R)^-1*((n%:R-1)*(n%:R-1)^-1)=
      (n%:R* n%:R^-1)*(n%:R-1)^-1-n%:R^-1*(n%:R-1)^-1 by ring.
  rewrite hAlgebra hNCancel !mul1r mulr1 in hScaled.
  exact:hScaled.
have hComparison:((n%:R-1)^-1< (3/2)* n%:R^-1:>R) by nra.
exact:lt_trans hComparison hChord.
Qed.
End Chord.

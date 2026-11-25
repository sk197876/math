(** Federer (1969), 3.3.19, p. 302: elementary
    angular order used in comparing actual sibling and
    different-parent disc gaps. All consequences follow from
    the already sealed scalar circular laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularCosineReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Order.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_cosine_quarter_turn]: zero cosine
    at pi/2, supporting the actual cyclic geometry of
    3.3.19, p. 302. It follows from the unit identity
    and the independently specified sine peak. *)
Lemma circular_cosine_quarter_turn:C (p/2)= 0.
Proof.
have hh:=circular_trig_unit ht (p/2);rewrite (real_sine_peak hb) in hh;nra.
Qed.

(** Source for [circular_sine_reflected_cosine]: exact
    sine/cosine reflection used in the angular estimates
    for 3.3.19, p. 302. *)
Lemma circular_sine_reflected_cosine x:C (p/2-x)=S x.
Proof.
by rewrite circular_cosine_difference circular_cosine_quarter_turn
  (real_sine_peak hb) mul0r mul1r add0r.
Qed.

(** Source for [circular_sine_weak_increase]: sine increases
    on the original first-quadrant interval, supporting
    the comparison of cyclic child gaps in 3.3.19, p. 302. *)
Lemma circular_sine_weak_increase a b:
  0<=a ->a<=b ->b<=p/2 ->S a<=S b.
Proof.
move=>ha hab hbp;have hp:=real_trigonometry_pi_positive hb.
rewrite -(circular_sine_reflected_cosine a) -(circular_sine_reflected_cosine b).
apply:(@circular_cosine_weak_decrease R (p/2-b) (p/2-a));lra.
Qed.

(** Source for [circular_sine_eighth_turn_upper]: supporting
    rational bound sin(pi/4)<= 3/4 in the actual child-gap
    comparisons for 3.3.19, p. 302. The sharper square
    identity follows from the addition and unit laws. *)
Lemma circular_sine_eighth_turn_upper:S (p/4)<= 3/4.
Proof.
have hAngle:p/2=p/4+p/4 by field.
have hCos:C (p/4+p/4)= 0 by rewrite -hAngle;exact:circular_cosine_quarter_turn.
rewrite (circular_trig_cosine_add ht) in hCos.
have hUnit:=circular_trig_unit ht (p/4);nra.
Qed.

(** Source for [circular_sine_triple_angle]: elementary
    triple-angle identity supporting exact child-gap
    comparisons in 3.3.19, p. 302. *)
Lemma circular_sine_triple_angle x:S (3* x)= 3* S x-4*(S x)^+3.
Proof.
have hAngle:3* x=x+x+x by ring.
rewrite hAngle !(circular_trig_sine_add ht) (circular_trig_cosine_add ht).
have hScaled:=congr1 (fun z:R=>S x* z) (circular_trig_unit ht x).
nra.
Qed.

(** Source for [circular_sine_twelfth_turn]: exact
    sin(pi/6)= 1/2, supporting the comparison with earlier
    parent gaps in 3.3.19, p. 302. Positivity selects
    the correct root of the triple-angle identity. *)
Lemma circular_sine_twelfth_turn:S (p/6)= 1/2.
Proof.
have hp:=real_trigonometry_pi_positive hb.
have h6:(0<(6:R)) by rewrite ltr0n.
have hx:0<p/6 by rewrite divr_gt0.
have hxp:p/6<p by lra.
have hS:=@circular_trig_sine_positive R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht (p/6) hx hxp.
have hAngle:3*(p/6)=p/2 by field.
have hTriple:=@circular_sine_triple_angle (p/6).
rewrite hAngle (real_sine_peak hb) in hTriple.
have hPolynomial:(S (p/6)+1)*(2* S (p/6)-1)^+2= 0 by nra.
have hNonzero:S (p/6)+1!= 0 by rewrite gt_eqF //;lra.
have hSquare:(2* S (p/6)-1)^+2= 0.
  apply:(mulfI hNonzero);by rewrite mulr0.
nra.
Qed.
End Order.

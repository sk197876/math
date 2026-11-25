(** Federer (1969), 3.1.24, p. 240: the
    explicitly solved quadratic expression really inverts the
    rational scalar majorant wherever both formulae are defined. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import ScalarAnalyticFraction ScalarInverseMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_inverse_majorant_scaled_value]: multiply
    the scalar inverse formula by gamma, supporting the quadratic
    substitution in Federer 3.1.24, p. 240. The positive
    parameters ensure both fixed denominators are nonzero. *)
Lemma scalar_inverse_majorant_scaled_value (R:realType) (b g x:R) :
  0<b -> 0<g -> g*scalar_inverse_majorant b g x=
    (x+b-Num.sqrt (scalar_inverse_discriminant b x))/(2*(b+1)).
Proof.
move=>hb hg.
have hb1:0<b+1 by rewrite addr_gt0 // ltr01.
have hb0:b+1!=0 by rewrite gt_eqF.
have hg0:g!=0 by rewrite gt_eqF.
rewrite /scalar_inverse_majorant; by field; rewrite hb0 hg0.
Qed.

(** Source for [scalar_inverse_majorant_quadratic_equation]:
    the quadratic equation solved by the displayed f in
    Federer 3.1.24, p. 240. The actual positive
    discriminant supplies the square-root identity. *)
Lemma scalar_inverse_majorant_quadratic_equation (R:realType) (b g x:R) :
  0<b -> 0<g -> scalar_inverse_majorant_domain b x ->
  (b+1)*(g*scalar_inverse_majorant b g x)^+2-
    (x+b)*(g*scalar_inverse_majorant b g x)+x=0.
Proof.
move=>hb hg hx.
have hb1:0<b+1 by rewrite addr_gt0 // ltr01.
have hb0:b+1!=0 by rewrite gt_eqF.
pose s:=Num.sqrt (scalar_inverse_discriminant b x).
have hsq:s^+2= scalar_inverse_discriminant b x:=sqr_sqrtr (ltW hx).
have he:(b+1)*((x+b-s)/(2*(b+1)))^+2-
    (x+b)*((x+b-s)/(2*(b+1)))+x=
    (s^+2-scalar_inverse_discriminant b x)/(4*(b+1)).
  rewrite /scalar_inverse_discriminant; by field; rewrite hb0.
rewrite (scalar_inverse_majorant_scaled_value x hb hg) he hsq subrr mul0r.
reflexivity.
Qed.

(** Source for [scalar_forward_majorant_zero]: the scalar
    majorant g used in Federer 3.1.24, p. 240,
    also passes through the origin. *)
Lemma scalar_forward_majorant_zero (R:realType) (b g:R) :
  scalar_forward_majorant b g 0=0.
Proof. by rewrite /scalar_forward_majorant mulr0 scalar_analytic_fraction_zero subrr. Qed.

(** Source for [scalar_majorant_right_inverse]: substituting
    the explicit f into the scalar g gives x, supporting
    the inverse-majorant derivative recurrence in Federer
    3.1.24, p. 240. Both actual domains are explicit;
    no reciprocal value is assigned at a pole. *)
Theorem scalar_majorant_right_inverse (R:realType) (b g x:R) :
  0<b -> 0<g -> scalar_inverse_majorant_domain b x ->
  scalar_analytic_fraction_domain g (scalar_inverse_majorant b g x) ->
  scalar_forward_majorant b g (scalar_inverse_majorant b g x)= x.
Proof.
move=>hb hg hx hdom.
pose z:=g*scalar_inverse_majorant b g x.
have hq:(b+1)*z^+2-(x+b)*z+x=0:=scalar_inverse_majorant_quadratic_equation hb hg hx.
have hd:1-z!=0.
  move:hdom; rewrite /scalar_analytic_fraction_domain -/z.
  have he:-g*scalar_inverse_majorant b g x+1= 1-z by rewrite /z; ring.
  by rewrite he.
have he:(b+1)*z-z/(1-z)-x= -((b+1)*z^+2-(x+b)*z+x)/(1-z).
  by field; exact hd.
rewrite hq oppr0 mul0r in he.
have heq:(b+1)*z-z/(1-z)= x.
  apply/eqP; rewrite -subr_eq0; exact/eqP.
rewrite /scalar_forward_majorant (scalar_analytic_fraction_value hdom) -mulrA.
change ((b+1)*z-z/(1-z)= x); exact heq.
Qed.

(** Federer (1969), 3.4.10, p. 338,
    citing Bruhat and Whitney, section 11(c),
    p. 159: two actual surface curves
    through every positive z-axis point. They
    will supply independent tangent directions; this
    file proves their original polynomial membership. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import GrassmannAbbreviations BruhatWhitneySurfaceUP
  BruhatWhitneySurfaceSealed BruhatWhitneySurfaceAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_positive_curve]: an
    explicit local curve on the original
    surface, supporting the example in 3.4.10,
    p. 338. Choose either sign
    of s with s^2=b; its coordinates
    are (st,t,b(1+sqrt(1+4t))/2). *)
Definition bruhat_whitney_positive_curve (R:realType) (b s t:R):R_n R 3:=
  [ffun i=>if i==ord0 then s*t else if i==Ordinal (isT:(1<3)%N)
    then t else b*(1+Num.sqrt (1+4*t))/2].

(** Source for [bruhat_whitney_positive_curve_base]: both
    signed curves pass through the actual
    original axis point (0,0,b), supporting
    3.4.10, p. 338. *)
Lemma bruhat_whitney_positive_curve_base (R:realType) (b s:R):
  @bruhat_whitney_positive_curve R b s 0 ord0=0 /\
  @bruhat_whitney_positive_curve R b s 0 (Ordinal (isT:(1<3)%N))=0 /\
  @bruhat_whitney_positive_curve R b s 0 ord_max=b.
Proof.
rewrite /bruhat_whitney_positive_curve !ffunE /= !mulr0 addr0 sqrtr1.
split;first reflexivity.
split;first reflexivity.
field;rewrite ?pnatr_eq0 //.
Qed.

(** Source for [bruhat_whitney_positive_curve_membership]: the
    two signed curves are actual points
    of the original polynomial surface, not
    assumed tangent witnesses, supporting the example
    cited in 3.4.10, p. 338.
    The closed discriminant endpoint is retained. *)
Theorem bruhat_whitney_positive_curve_membership (R:realType) (b s t:R):
  s^+2=b ->0<= 1+4*t ->
  @BruhatWhitneySurface.set R (@bruhat_whitney_positive_curve R b s t).
Proof.
move=>hS hDiscriminant.
have hS4:s^+4=b^+2 by rewrite -hS -exprM.
have hRoot:(Num.sqrt (1+4*t))^+2= 1+4*t:=sqr_sqrtr hDiscriminant.
have hEquation:@bruhat_whitney_surface_equation R
    (@bruhat_whitney_positive_curve R b s t)=
    b^+2*t^+3*(1+4*t-(Num.sqrt (1+4*t))^+2)/4.
  rewrite /bruhat_whitney_surface_equation /bruhat_whitney_positive_curve !ffunE /=
    !exprMn hS hS4.
  field;rewrite ?pnatr_eq0 //.
apply/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R)).
change (@bruhat_whitney_surface_equation R (@bruhat_whitney_positive_curve R b s t)=0).
by rewrite hEquation hRoot subrr mulr0 mul0r.
Qed.

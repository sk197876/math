(** Inner-product geometry for Federer (1969), 2.10.30, p. 195: normal line
    coordinates and reflection rho_u(x)=x-2(x.u)u. The statements are
    derived from the project's inner-product laws, without
    finite-dimensional or coordinate assumptions. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws OrthonormalFamilies Bilinear
  InnerNorm InnerNormInequalities OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalGeometry.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation c := (inner_coordinate hB).
Local Notation hb := (inner_bilinear hB).

(** Source for [is_unit_normal]: supporting abstract
    characterisation of the unit vector orthogonal to the
    hyperplane V in 2.10.30, p. 195. The set H
    is its entire orthogonal hyperplane, not just a
    subset on which the coordinate happens to vanish. *)
Definition is_unit_normal (H : set V) (u : V) :=
  B u u= 1 /\ forall x, H x <-> c u x=0.

(** Source for [normal_foot]: supporting orthogonal hyperplane component of
    x in 2.10.30, p. 195 *)
Definition normal_foot (u x : V) := x-(c u x)*:u.

(** Source for [normal_reflection]: direct formula for
    rho_u in 2.10.30, p. 195. Linearity is
    proved before the orthogonal-map assertion. *)
Definition normal_reflection (u x : V) := x-(2*c u x)*:u.

(** Source for [normal_foot_linear]: supporting linearity of the orthogonal
    projection in 2.10.30, p. 195 *)
Lemma normal_foot_linear u : linear (normal_foot u).
Proof.
move=> a x y; rewrite /normal_foot linearP /= scalerDl scalerBr scalerA.
by rewrite opprD addrACA.
Qed.
HB.instance Definition _ u := GRing.isLinear.Build R V V *:%R
  (normal_foot u) (normal_foot_linear u).

(** Source for [normal_reflection_linear]: supporting
    linearity of the displayed reflection in 2.10.30,
    p. 195, proved from its intrinsic formula. *)
Lemma normal_reflection_linear u : linear (normal_reflection u).
Proof.
move=> a x y; rewrite /normal_reflection linearP /= mulrDr mulrCA
  scalerDl scalerBr scalerA opprD addrACA.
by [].
Qed.
HB.instance Definition _ u := GRing.isLinear.Build R V V *:%R
  (normal_reflection u) (normal_reflection_linear u).

Variable u : V.
Hypothesis hu : B u u= 1.

(** Source for [unit_normal_norm]: supporting equivalence
    of unit squared length and unit length for the
    normal in 2.10.30, p. 195. *)
Lemma unit_normal_norm : inner_norm hB u= 1.
Proof. apply: inner_norm_value; [exact: ler01|by rewrite hu expr1n]. Qed.

(** Source for [normal_coordinate_foot]: supporting
    orthogonality of the hyperplane component in
    2.10.30, p. 195. *)
Lemma normal_coordinate_foot x : c u (normal_foot u x)=0.
Proof.
rewrite /normal_foot linearB linearZ (inner_coordinateE hB u u) hu.
change (c u x-(c u x)*1=0).
by rewrite mulr1 subrr.
Qed.

(** Source for [normal_decomposition]: supporting unique line decomposition
    of a point for 2.10.30, p. 195 *)
Lemma normal_decomposition x : normal_foot u x+(c u x)*:u=x.
Proof. by rewrite /normal_foot subrK. Qed.

(** Source for [normal_line_coordinate]: supporting
    scalar coordinate on the perpendicular line through
    y in 2.10.30, p. 195. *)
Lemma normal_line_coordinate y t : c u y=0 -> c u (y+t*:u)=t.
Proof.
move=> hy; rewrite linearD linearZ (inner_coordinateE hB u u) hu hy.
change (0+t*1=t); by rewrite mulr1 add0r.
Qed.

(** Source for [normal_line_foot]: supporting constant hyperplane component
    on a normal line in 2.10.30, p. 195 *)
Lemma normal_line_foot y t : c u y=0 -> normal_foot u (y+t*:u)=y.
Proof. by move=> hy; rewrite /normal_foot (normal_line_coordinate t hy) addrK. Qed.

(** Source for [normal_reflection_coordinate]: supporting
    sign reversal of the normal coordinate under rho_u
    in 2.10.30, p. 195. *)
Lemma normal_reflection_coordinate x : c u (normal_reflection u x)= -c u x.
Proof.
rewrite /normal_reflection linearB linearZ (inner_coordinateE hB u u) hu.
change (c u x-(2*c u x)*1= -c u x).
ring.
Qed.

(** Source for [normal_reflection_foot]: supporting
    preservation of the hyperplane component under rho_u
    in 2.10.30, p. 195. *)
Lemma normal_reflection_foot x : normal_foot u (normal_reflection u x)=normal_foot u x.
Proof.
rewrite /normal_foot normal_reflection_coordinate /normal_reflection scaleNr opprK.
have he : 2*c u x=c u x+c u x by ring.
by rewrite he scalerDl opprD addrA subrK.
Qed.

(** Source for [normal_reflectionK]: supporting involution
    law of the reflection in 2.10.30, p. 195.
    It also supplies surjectivity without a chosen inverse. *)
Lemma normal_reflectionK : involutive (normal_reflection u).
Proof.
move=> x.
change (normal_reflection u x-(2*c u (normal_reflection u x))*:u=x).
rewrite normal_reflection_coordinate /normal_reflection mulrN scaleNr opprK.
exact: subrK.
Qed.

(** Source for [normal_reflection_orthogonal]: direct
    rho_u in O(n) assertion in 2.10.30, p. 195,
    here proved for any real inner-product space.
    No external reflection or orthogonal-group theorem is used. *)
Theorem normal_reflection_orthogonal :
  is_orthogonal_map B B (GRing.Linear.clone _ _ _ _ (normal_reflection u) _).
Proof.
move=> x y.
change (B (normal_reflection u x) (normal_reflection u y)=B x y).
rewrite /normal_reflection (bilBl hb) !(bilBr hb) !(bilZl hb) !(bilZr hb).
change (B x y-(2*c u y)*B x u-((2*c u x)*B u y-(2*c u x)*((2*c u y)*B u u))=B x y).
rewrite hu (inner_symmetric hB u y) -(inner_coordinateE hB u y) -(inner_coordinateE hB u x).
ring.
Qed.

(** Source for [normal_line_norm_square]: supporting Pythagorean
    line-coordinate identity used for the containing-ball and boundary
    assertions in 2.10.30, p. 195 *)
Lemma normal_line_norm_square y t : c u y=0 ->
  inner_norm hB (y+t*:u)^+2=inner_norm hB y^+2+t^+2.
Proof.
move=> hy; rewrite !inner_norm_sqr (inner_sum_square hB) (inner_scale_square hB) hu mulr1.
have ho : B y (t*:u)=0.
  rewrite (bilZr hb); change (t*B y u=0).
  by rewrite -(inner_coordinateE hB u y) hy mulr0.
by rewrite ho !add0r addr0.
Qed.

(** Source for [normal_coordinate_bound]: supporting
    boundedness of scalar normal sections in 2.10.30,
    p. 195, from the already proved Cauchy inequality. *)
Lemma normal_coordinate_bound x : `|c u x|<=inner_norm hB x.
Proof.
rewrite inner_coordinateE.
have hh := @inner_cauchy R V B hB x u.
by rewrite unit_normal_norm mulr1 in hh.
Qed.
End NormalGeometry.

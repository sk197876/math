(** Reflection along a sphere chord supporting Federer (1969), 2.10.31, pp.
    195–196. For two distinct points of the same origin-centred sphere, the
    unit normal in their difference direction reflects the first point to
    the second. This is the geometric identity used to move the missing cap
    in the finite symmetrisation argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormalization OrthonormalFamilies
  Bilinear UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_chord_reflection]: direct supporting
    identity rho_u(a)=y_j for
    u=(y_j-a)/abs(y_j-a) in 2.10.31,
    p. 196. It uses only the equal-radius
    condition and distinctness, not finite dimension. *)
Theorem unit_chord_reflection (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a y : V) :
  a!=y -> inner_norm hB a=inner_norm hB y ->
  let u := inner_normalize hB (y-a) in
  B u u= 1 /\ normal_reflection hB u a=y.
Proof.
move=> hay hnorm u.
pose w := y-a.
pose d := inner_norm hB w.
have hw : w!=0 by rewrite /w subr_eq0 eq_sym.
have hdpos : 0<d by rewrite /d inner_norm_gt0.
have hd : d!=0 by rewrite (gt_eqF hdpos).
have hd2 : d^+2!=0 by rewrite expf_eq0 hd.
have he : a+w=y by rewrite /w addrC subrK.
have hsq := inner_sum_square hB a w.
rewrite he -(inner_norm_sqr hB y) -(inner_norm_sqr hB a) -(inner_norm_sqr hB w) -hnorm in hsq.
have hcoef0 : 2*B a w= -(d^+2) by rewrite /d; lra.
have heq : (2*(d^-1*B a w))*d^-1=(2*B a w)*(d^-1*d^-1) by ring.
have hinv : d^-1*d^-1=(d^+2)^-1 by rewrite expr2 invfM.
have hcoef : (2*(d^-1*B a w))*d^-1= -1.
  by rewrite heq hinv hcoef0 mulNr mulfV.
split.
- exact (@inner_normalize_square R V B hB w hw).
- rewrite /normal_reflection inner_coordinateE.
  have hu : u=d^-1*:w by [].
  rewrite hu (bilZr (inner_bilinear hB)).
  change (a-(2*(d^-1*B a w))*:(d^-1*:w)=y).
  by rewrite scalerA hcoef scaleN1r opprK he.
Qed.

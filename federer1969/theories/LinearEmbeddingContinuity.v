(** Federer (1969), 3.1.21, p. 234: the positive lower
    bound is equivalent to continuity of the linear inverse on
    its actual range, without an inverse on the whole target. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP RealNormNormalization TangentEmbeddingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_linear_inverse_continuous]: the linear
    homeomorphism onto its range in Federer 3.1.21, p. 234,
    expressed by inverse continuity at zero. Homogeneity gives
    continuity everywhere, and this criterion itself forces
    injectivity; the range is not assumed complemented. *)
Definition norm_linear_inverse_continuous (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (L:Hom X Y) :=
  forall e:R,0<e -> exists d:R,0<d /\
    forall x,NY (L x)<d -> NX x<e.

(** Source for [norm_linear_inverse_lower_boundP]: supporting
    equivalence of the printed linear-homeomorphism hypothesis
    and the intrinsic homogeneous lower-bound form used for the
    reverse tangent inclusion, Federer 3.1.21, p. 234. *)
Lemma norm_linear_inverse_lower_boundP (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (L:Hom X Y) :
  norm_linear_inverse_continuous NX NY L <-> norm_linear_lower_bound NX NY L.
Proof.
split.
- move=>hi.
  have [d [hd hsmall]]:=hi 1 ltr01.
  exists d; split=>// x.
  case:(eqVneq x 0)=>[->|hx].
  + by rewrite linear0 (real_seminorm_zero hNX.1) (real_seminorm_zero hNY.1) mulr0.
  have hnx:0<NX x by rewrite (real_norm_positive hNX.1 hNX.2).
  have hunit:NX (real_norm_normalize NX x)= 1.
    by rewrite (real_norm_normalize_value hNX.1) (gt_eqF hnx).
  have hb:d<=NY (L (real_norm_normalize NX x)).
    rewrite leNgt; apply/negP=>hh.
    have hbad:=hsmall _ hh; by rewrite hunit ltxx in hbad.
  rewrite /real_norm_normalize linearZ /= (real_seminorm_scale hNY.1)
    normfV (ger0_norm (ltW hnx)) mulrC in hb.
  move: hb; by rewrite ler_pdivlMr // mulrC.
- move=>[c [hc hb]] e he.
  exists (c*e); split; first exact: mulr_gt0.
  move=>x hx; have hh:=le_lt_trans (hb x) hx.
  by move: hh; rewrite ltr_pM2l.
Qed.

(** Source for [norm_linear_lower_bound_injective]: a linear
    homeomorphism onto its image is injective, supporting the
    tangent-image equality in Federer 3.1.21, p. 234. *)
Lemma norm_linear_lower_bound_injective (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (L:Hom X Y) : norm_linear_lower_bound NX NY L -> injective L.
Proof.
move=>[c [hc hb]] x y hxy.
have hh:=hb (x-y).
rewrite linearB /= hxy subrr (real_seminorm_zero hNY.1) in hh.
have hn:=real_seminorm_nonnegative hNX.1 (x-y).
have hz:NX (x-y)=0 by nra.
have he:=hNX.2 _ hz; apply/eqP; by rewrite -subr_eq0 he.
Qed.

(** Federer (1969), 3.1.1, p. 209: the differential is determined by all
    directional difference quotients. The proof uses only the abstract
    norm laws and the epsilon remainder specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_directional_limit]: Federer 3.1.1,
    p. 209, second displayed formula. In words: along every direction v,
    the quotients (f(a+t v)-f(a))/t converge to L(v). *)
Theorem norm_differential_directional_limit (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L -> forall v,
    punctured_norm_limit NY (fun t => t^-1 *: (f (a+t *: v)-f a)) (L v).
Proof.
move=> hf v e he.
have hn := real_seminorm_nonnegative hNX.1 v.
have hn1 : 0 < NX v+1 by lra.
have he' : 0 < e/(NX v+1) by rewrite divr_gt0.
have [r [hr hA]] := norm_differential_interior hf.
have [d [hd hrem]] := norm_differential_remainder hf he'.
pose c := Num.min r d.
have hc : 0 < c by rewrite /c lt_min hr hd.
exists (c/(NX v+1)); split; first by rewrite divr_gt0.
move=> t /andP [ht hsmall].
have ht0 : t != 0 by move: ht; rewrite normr_gt0.
have htN : `|t| * (NX v+1) < c.
  by move: hsmall; rewrite ltr_pdivlMr.
have hinc : NX (t *: v) < c.
  rewrite (real_seminorm_scale hNX.1).
  apply: le_lt_trans _ htN.
  by rewrite ler_wpM2l // lerDl.
have hcr : c <= r by rewrite /c ge_min lexx.
have hcd : c <= d by rewrite /c ge_min lexx orbT.
have hb := hrem (t *: v) (hA _ (lt_le_trans hinc hcr))
  (lt_le_trans hinc hcd).
have heq : t^-1 *: (f (a+t *: v)-f a)-L v =
    t^-1 *: (f (a+t *: v)-f a-L (t *: v)).
  by rewrite [RHS]scalerBr [L (_ *: _)]linearZ /= scalerA mulVf // scale1r.
rewrite heq (real_seminorm_scale hNY.1).
apply: le_lt_trans (ler_wpM2l (normr_ge0 _) hb) _.
rewrite (real_seminorm_scale hNX.1) normfV.
have hcancel : `|t|^-1 * (e/(NX v+1) * (`|t| * NX v)) =
    e/(NX v+1) * NX v.
  rewrite mulrCA; congr (_ * _).
  by rewrite mulrA mulVf ?mul1r // normr_eq0.
rewrite hcancel.
have hl : e/(NX v+1) * NX v < e/(NX v+1) * (NX v+1).
  by rewrite ltr_pM2l // ltrDl.
apply: lt_le_trans hl _.
by rewrite divfK ?lexx //; exact: lt0r_neq0 hn1.
Qed.

(** Source for [norm_differential_unique]: Federer 3.1.1, p. 209:
    the continuous linear map L is uniquely determined by the directional
    quotient formula. This includes a zero-dimensional source or target. *)
Theorem norm_differential_unique (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) (L M : Hom X Y) :
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY A f a M -> L=M.
Proof.
move=> hL hM; apply: hom_ext=> v.
exact: (punctured_norm_limit_unique hNY
  (norm_differential_directional_limit hNX hNY hL v)
  (norm_differential_directional_limit hNX hNY hM v)).
Qed.

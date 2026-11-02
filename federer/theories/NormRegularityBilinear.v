(** Federer (1969), 3.1.20, p. 232: class-k interpolation in
    a convex coordinate neighbourhood. The calculus is the already
    proved bounded bilinear class law of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormBoundedBilinearUP NormClassHigherBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_bilinear]: bounded bilinear operations
    preserve class k, 3.1.11, p. 220, supporting the interpolated
    chart formula in Federer 3.1.20, p. 232. Representation adapter
    using only the public sealed multilinear spaces. *)
Lemma norm_class_bilinear (R:realType) (X U V W:lmodType R)
    (NX:X->R) (NU:U->R) (NV:V->R) (NW:W->R)
    (hNX:is_real_norm NX) (hNU:is_real_norm NU) (hNV:is_real_norm NV) (hNW:is_real_norm NW)
    (A:X->Prop) (f:X->U) (g:X->V) (B:U->V->W) k :
  norm_bounded_bilinear NU NV NW B ->
  norm_class hNX hNU A f k -> norm_class hNX hNV A g k ->
  norm_class hNX hNW A (fun x=>B (f x) (g x)) k.
Proof.
exact (@norm_class_higher_bilinear R X NX hNX k U V W NU NV NW hNU hNV hNW
  (fun j=>@ContinuousMultilinear.space R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.space R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.space R j X W NX NW hNX hNW)
  (fun j=>@ContinuousMultilinear.evaluation R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.norm R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.evaluation R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.norm R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.evaluation R j X W NX NW hNX hNW)
  (fun j=>@ContinuousMultilinear.norm R j X W NX NW hNX hNW)
  (fun j=>@ContinuousMultilinear.laws R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.laws R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.laws R j X W NX NW hNX hNW) A f g B).
Qed.

(** Source for [norm_class_scalar_product]: the products u_s phi
    in the retraction-patching formula, Federer 3.1.20, p. 232,
    have class k by the bilinear law. The scalar norm is absolute value. *)
Lemma norm_class_scalar_product (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (u:X->R^o) (f:X->Y) k :
  norm_class hNX (scalar_absolute_value_norm R) A u k ->
  norm_class hNX hNY A f k ->
  norm_class hNX hNY A (fun x=>(u x)*:f x) k.
Proof.
move=>hu hf.
have hB:norm_bounded_bilinear (fun t:R^o=>`|t|) NY NY (fun t y=>t*:y).
  split.
  - split.
    + move=>y c t s; by rewrite scalerDl scalerA.
    + move=>t c x y; by rewrite scalerDr !scalerA mulrC.
  - exists 1; split; first exact: ler01.
    move=>t y; by rewrite (real_seminorm_scale hNY.1) mul1r.
exact: norm_class_bilinear hB hu hf.
Qed.

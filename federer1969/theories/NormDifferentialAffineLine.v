(** Federer (1969), 3.1.11, pp. 220–221:
    restriction to the affine path a+t(x-a).
    The path is the one corrected in the
    erratum, p. 4, book p. 221 line 1. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialChain
  NormDifferentialLocalAgreement NormClassOneUP NormHigherCurveDerivativeUP
  NormedPrimitiveCell.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [affine_line_increment]:
    increments of the Taylor path a+t v,
    supporting Federer 3.1.11, p. 221.
    For the printed path v is x-a. *)
Lemma affine_line_increment (R : realType) (X : lmodType R)
    (a v : X) (t s : R) :
  a+(t+s)*:v=(a+t*:v)+s*:v.
Proof. by rewrite scalerDl addrA. Qed.

(** Source for [norm_affine_line_differential]:
    the path a+t v has derivative v,
    as used to compute the Taylor path derivatives
    in Federer 3.1.11, p. 221. *)
Lemma norm_affine_line_differential (R : realType) (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) (a v : X) t :
  has_norm_differential (fun s : R^o=>`|s|) NX (fun _=>True)
    (fun s=>a+s*:v) t (scalar_coefficient_linear_map v).
Proof.
split.
- exists 1; split; first exact: ltr01; by [].
- exact: scalar_coefficient_linear_bound hNX v.
- move=> e he; exists 1; split; first exact: ltr01.
  move=> s _ _; change (NX ((a+(t+s)*:v)-(a+t*:v)-s*:v)<=e*`|s|).
  rewrite affine_line_increment addrAC addrK subrr (real_seminorm_zero hNX.1).
  exact: mulr_ge0 (ltW he) (normr_ge0 s).
Qed.

(** Source for [norm_differential_along_affine_line]:
    the first chain-rule step for
    g(t)=f(a+t v), Federer 3.1.11,
    p. 221. Its domain is the actual
    preimage of the domain of f under the path. *)
Lemma norm_differential_along_affine_line (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) (a v : X) t (L : Hom X Y) :
  has_norm_differential NX NY A f (a+t*:v) L ->
  has_norm_differential (fun s : R^o=>`|s|) NY
    (fun s=>A (a+s*:v)) (fun s=>f (a+s*:v)) t
    (hom_comp L (scalar_coefficient_linear_map v)).
Proof.
move=> hf.
have hc := norm_differential_chain (@scalar_absolute_value_norm R) hNX hNY
  (norm_affine_line_differential hNX a v t) hf.
apply: (@norm_differential_local_agreement R R^o Y
  (fun s : R^o=>`|s|) NY (@scalar_absolute_value_norm R)
  (fun s=>True /\ A (a+s*:v)) (fun s=>A (a+s*:v))
  (fun s=>f (a+s*:v)) (fun s=>f (a+s*:v)) t
  (hom_comp L (scalar_coefficient_linear_map v)) 1 ltr01 _ _ hc).
- by move=> h _; split=> [[_ hh]|hh].
- by move=> h _ _.
Qed.

(** Source for [norm_class_zero_along_affine_line]:
    continuity on the actual open parameter domain
    of the Taylor path, Federer 3.1.11,
    pp. 220–221. This also covers the
    constant path v= 0 without division by its norm. *)
Theorem norm_class_zero_along_affine_line (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (A : X->Prop) (f : X->Y) (a v : X) :
  norm_class_zero NX NY A f ->
  norm_class_zero (fun s : R^o=>`|s|) NY
    (fun s=>A (a+s*:v)) (fun s=>f (a+s*:v)).
Proof.
move=> hf t ht.
have hv := real_seminorm_nonnegative hNX.1 v.
have hden : 0<NX v+1 by lra.
have hsmall (r : R) : 0<r -> forall s, `|s|<r/(NX v+1) -> NX (s*:v)<r.
  move=> hr s hs.
  rewrite (real_seminorm_scale hNX.1).
  have hp : 0<r/(NX v+1) by rewrite divr_gt0.
  have hn := normr_ge0 s.
  have hid : (r/(NX v+1))*(NX v+1)=r by rewrite divfK // gt_eqF.
  nra.
have [hi hc] := hf (a+t*:v) ht.
split.
- have [r [hr hball]] := hi.
  exists (r/(NX v+1)); split; first by rewrite divr_gt0.
  move=> s hs; rewrite affine_line_increment.
  exact: hball (s*:v) (hsmall r hr s hs).
- move=> e he; have [d [hd hmod]] := hc e he.
  exists (d/(NX v+1)); split; first by rewrite divr_gt0.
  move=> s hs hsd.
  rewrite affine_line_increment in hs.
  rewrite affine_line_increment.
  exact: hmod (s*:v) hs (hsmall d hd s hsd).
Qed.

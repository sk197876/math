(** Federer (1969), 3.4.2(7), p. 314: injectivity of the
    differential of the joint scalar and projection map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormHigherCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_joint_linear_map]: the differential
    (DF,q) in 3.4.2(7), p. 314, written in the original space
    through the section j and the kernel vector v. The formula
    j(q(w))+DF(w)v is a linear change of target coordinates for
    the printed joint map. It uses only public linear operations. *)
Definition critical_joint_linear_map (R:realType) (V W:lmodType R)
    (q:Hom V W) (j:Hom W V) (D:Hom V R^o) (v:V):Hom V V:=
  hom_comp j q+hom_comp (scalar_coefficient_linear_map v) D.

(** Source for [critical_joint_linear_projection]: projection onto
    q coordinates recovers q from the joint differential, supporting
    the kernel calculation in 3.4.2(7), p. 314. *)
Lemma critical_joint_linear_projection (R:realType) (V W:lmodType R)
    (q:Hom V W) (j:Hom W V) (D:Hom V R^o) v:
  cancel j q ->q v=0 ->forall w,q (critical_joint_linear_map q j D v w)=q w.
Proof.
move=>hSection hV w.
change (q (j (q w)+D w*:v)=q w).
by rewrite (Bilinear.linD (hom_linear q)) hSection
  (Bilinear.linZ (hom_linear q)) hV scaler0 addr0.
Qed.

(** Source for [critical_joint_linear_injective]: the kernel
    calculation ker(Dg)=ker(DF) intersect ker(q)={0} in 3.4.2(7),
    p. 314. The nonzero derivative on the kernel line excludes
    its remaining nonzero vectors. This includes the case where
    the projection has zero-dimensional target. *)
Theorem critical_joint_linear_injective (R:realType) (V W:lmodType R)
    (q:Hom V W) (j:Hom W V) (D:Hom V R^o) v:
  cancel j q ->q v=0 ->v!=0 ->D v!=0 ->
  (forall w,q w=0 ->exists t:R,w=t*:v) ->
  injective (critical_joint_linear_map q j D v).
Proof.
move=>hSection hV hv hD hKernel x y hEqual.
pose L:=critical_joint_linear_map q j D v.
change (L x=L y) in hEqual.
have hZero:L (x-y)=0 by rewrite (Bilinear.linB (hom_linear L)) hEqual subrr.
have hQ:q (x-y)=0.
  rewrite -(critical_joint_linear_projection D hSection hV (x-y)) hZero linear0.
  exact:erefl.
have [t hSpan]:=hKernel (x-y) hQ.
have hAtV:L v=D v*:v.
  change (j (q v)+D v*:v=D v*:v).
  by rewrite hV linear0 add0r.
rewrite hSpan (Bilinear.linZ (hom_linear L)) hAtV scalerA in hZero.
have hCoefficient:t*D v=0.
  apply/eqP;move/eqP:hZero;by rewrite scaler_eq0 (negbTE hv) orbF.
have ht:t=0.
  apply/eqP;move/eqP:hCoefficient;by rewrite mulf_eq0 (negbTE hD) orbF.
have hDifference:x-y=0 by rewrite hSpan ht scale0r.
by apply/eqP;rewrite -subr_eq0 hDifference.
Qed.

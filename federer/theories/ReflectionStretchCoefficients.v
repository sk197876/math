(** Scalar connection for the coordinate-stretch proof
    supporting Federer (1969), 3.2.45,
    pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reflection_stretch_coefficients]: supporting
    scalar identity for the anisotropic coefficient
    comparison in Federer 3.2.45,
    pp. 279–280. The weights
    a=(1+t)/2 and b=(1-t)/2
    sum to one, change the normal
    coordinate by factor t, and have
    absolute sum t when t>=1.
    This supplies only scalar identities; no
    volume or intrinsic comparison is assumed. *)
Lemma reflection_stretch_coefficients (R : realType) (t : R) :
  let a := (1+t)/2 in let b := (1-t)/2 in
  a+b= 1 /\ -2*b=t-1 /\ (1<=t -> `|a|+`|b|=t).
Proof.
move=> a b.
have hSum : a+b= 1 by rewrite /a /b; field; by rewrite ?pnatr_eq0.
have hCoefficient : -2*b=t-1 by rewrite /b; field; by rewrite ?pnatr_eq0.
split=> //; split=> // hT.
have hA : 0<=a by rewrite /a; lra.
have hB : b<=0 by rewrite /b; lra.
rewrite (ger0_norm hA) (ler0_norm hB); lra.
Qed.

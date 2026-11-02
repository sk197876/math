(** Federer (1969), 3.1.11, pp. 220–221:
    bounded linear evaluation preserves continuity of
    the derivative fields in the Taylor calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_postcompose]:
    continuity after a bounded linear contraction,
    supporting the path coefficients in Federer
    3.1.11, p. 221. The original
    open domain is preserved. *)
Lemma norm_class_zero_postcompose (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (hNY : is_real_norm NY) (A : X->Prop) (f : X->Y) (L : Hom Y Z) :
  norm_class_zero NX NY A f -> norm_bounded_linear NY NZ L ->
  norm_class_zero NX NZ A (fun x=>L (f x)).
Proof.
move=> hf [C [hC hL]] a ha; split; first exact: (hf a ha).1.
move=> e he.
have hden : 0<C+1 by lra.
have hp : 0<e/(C+1) by rewrite divr_gt0.
have [d [hd hb]] := (hf a ha).2 _ hp.
exists d; split=> // h hh hs.
rewrite -linearB; apply: le_lt_trans (hL _) _.
have hsmall := hb h hh hs.
have hn := real_seminorm_nonnegative hNY.1 (f (a+h)-f a).
have hid : (e/(C+1))*(C+1)=e by rewrite divfK // gt_eqF.
nra.
Qed.

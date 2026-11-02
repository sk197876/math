(** Federer (1969), 3.1.1, p. 210: translation and composition with
    the inverse differential reduce the inverse-function proof to the
    case a=f(a)=0 and Df(a)=identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialFiniteCalculus NormClassOneUP NormClassOneLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_translate]: supporting change of
    origins in Federer 3.1.1, p. 210. Translating the source and subtracting
    a fixed target value leave the differential unchanged. *)
Lemma norm_differential_translate (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (a x : X) (b : Y) (L : Hom X Y) :
  has_norm_differential NX NY A f (a+x) L ->
  has_norm_differential NX NY (fun z => A (a+z))
    (fun z => f (a+z)-b) x L.
Proof.
move=> hf; constructor.
- have [r [hr hb]] := norm_differential_interior hf.
  exists r; split=> // h hh; rewrite addrA; exact: hb.
- exact: norm_differential_bounded hf.
- move=> e he; have [d [hd hb]] := norm_differential_remainder hf he.
  exists d; split=> // h hh hs.
  rewrite addrA opprB addrA subrK.
  apply: hb=> //; by rewrite -addrA.
Qed.

(** Source for [norm_class_one_normalization]: the precise change
    of function used in Federer 3.1.1, p. 210. Any bounded linear map M
    can be composed after the translated function; its differential field
    is M composed with the translated original field. *)
Lemma norm_class_one_normalization (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNZ : is_real_norm NZ)
    (A : X -> Prop) (f : X -> Y) (D : X -> Hom X Y)
    (a : X) (b : Y) (M : Hom Y Z) :
  is_norm_class_one_field NX NY A f D -> norm_bounded_linear NY NZ M ->
  is_norm_class_one_field NX NZ (fun z => A (a+z))
    (fun z => M (f (a+z)-b)) (fun z => hom_comp M (D (a+z))).
Proof.
move=> hf hM.
have hdiff : forall x, A (a+x) ->
    has_norm_differential NX NZ (fun z => A (a+z))
      (fun z => M (f (a+z)-b)) x (hom_comp M (D (a+x))).
  move=> x hx; apply: (norm_differential_postcompose hNX _ hM).
  exact: (@norm_differential_translate R X Y NX NY A f a x b (D (a+x))
    (norm_class_one_differential hf hx)).
constructor=> //.
- exact: (norm_everywhere_differentiable_class_zero hNZ hdiff).
- move=> x hx e he; have [C [hC hMC]] := hM.
  have hp : 0 < e/(C+1) by rewrite divr_gt0 //; lra.
  have [d [hd hb]] := norm_class_one_continuity hf hx hp.
  exists d; split=> // h hh hs v.
  change (NZ (M (D (a+(x+h)) v)-M (D (a+x) v)) <= e*NX v).
  rewrite -linearB.
  apply: le_trans (hMC _) _.
  have hh' : A ((a+x)+h) by rewrite -addrA.
  have hbound := hb h hh' hs v.
  change (is_true (NY (D ((a+x)+h) v-D (a+x) v) <= (e/(C+1))*NX v)) in hbound.
  rewrite -addrA in hbound.
  apply: le_trans (ler_wpM2l hC hbound) _.
  have heq : e/(C+1)*(C+1) = e by rewrite divfK //; lra.
  have hp0 := ltW hp.
  have hc : C*(e/(C+1)) <= e by nra.
  rewrite mulrA; apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 v.
  exact hc.
Qed.

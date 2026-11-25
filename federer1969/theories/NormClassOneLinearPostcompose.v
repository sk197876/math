(** Federer (1969), 3.1.18, pp. 229–230: the field p Df is the
    continuous differential field of p composed with f. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialFiniteCalculus NormClassOneUP NormClassOneLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_linear_postcompose]: continuity and
    the actual differential p Df, used to keep rank(p Df)>=v on a
    neighbourhood in Federer 3.1.18, p. 230. This supporting bound
    applies to arbitrary normed spaces and bounded linear p. *)
Theorem norm_class_one_linear_postcompose (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (A:X->Prop) (f:X->Y) (D:X->Hom X Y) (p:Hom Y Z) :
  is_norm_class_one_field NX NY A f D -> norm_bounded_linear NY NZ p ->
  is_norm_class_one_field NX NZ A (fun x=>p (f x)) (fun x=>hom_comp p (D x)).
Proof.
move=>hD hp.
have hdiff x (hx:A x) : has_norm_differential NX NZ A (fun x=>p (f x)) x (hom_comp p (D x)).
  exact (@norm_differential_postcompose R X Y Z NX NY NZ hNX A f x (D x) p
    (norm_class_one_differential hD hx) hp).
constructor=>//.
- exact (@norm_everywhere_differentiable_class_zero R X Z NX NZ hNZ A
    (fun x=>p (f x)) (fun x=>hom_comp p (D x)) hdiff).
- move=>x hx e he.
  have [C [hC hb]]:=hp.
  have hden:0<C+1 by lra.
  have heps:0<e/(C+1) by rewrite divr_gt0.
  have [d [hd hcont]]:=norm_class_one_continuity hD hx heps.
  exists d; split=>// z hz hs u.
  change (NZ (p (D (x+z) u)-p (D x u))<=e*NX u).
  rewrite -linearB.
  apply: le_trans (hb _) _.
  have hc:=hcont z hz hs u.
  change (is_true (NY (D (x+z) u-D x u)<=e/(C+1)*NX u)) in hc.
  apply: le_trans (ler_wpM2l hC hc) _.
  have hn:=real_seminorm_nonnegative hNX.1 u.
  have heq:e/(C+1)*(C+1)=e by rewrite divfK // gt_eqF.
  have hcoef:C*(e/(C+1))<=e by nra.
  rewrite mulrA; apply: ler_wpM2r=>//; exact hcoef.
Qed.

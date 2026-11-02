(** Federer (1969), 3.1.11, pp. 220–222:
    continuity of a scalar times a normed-vector
    function, supporting the Taylor integrand and
    the Leibniz calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_scalar_product]:
    the continuity rule for the scalar-vector
    products appearing in Federer 3.1.11,
    pp. 220–222. It uses only the
    given norm laws, with no completeness assumption. *)
Theorem norm_class_zero_scalar_product (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNY : is_real_norm NY) (A : X->Prop)
    (f : X->R) (g : X->Y) :
  norm_class_zero NX (fun t : R^o=>`|t|) A f ->
  norm_class_zero NX NY A g ->
  norm_class_zero NX NY A (fun x=>f x*:g x).
Proof.
move=> hf hg a ha; split; first exact: (hf a ha).1.
move=> e he.
pose K := `|f a|+NY (g a)+2.
have hfa := normr_ge0 (f a).
have hga := real_seminorm_nonnegative hNY.1 (g a).
have hK : 0<K by rewrite /K; lra.
have heK : 0<e/K by rewrite divr_gt0.
pose p := Num.min 1 (e/K).
have hp : 0<p by rewrite /p lt_min ltr01 heK.
have hp1 : p<= 1 by rewrite /p ge_min lexx.
have hpe : p<=e/K by rewrite /p ge_min lexx orbT.
have [r [hr hrf]] := (hf a ha).2 _ hp.
have [s [hs hsg]] := (hg a ha).2 _ hp.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=> h hh; rewrite lt_min=>/andP [hhr hhs].
have hdf := hrf h hh hhr.
have hdg := hsg h hh hhs.
have hvalue : `|f (a+h)|<=`|f a|+1.
  have ht := ler_normD (f a) (f (a+h)-f a).
  rewrite addrC subrK in ht; lra.
have hid : f (a+h)*:g (a+h)-f a*:g a=
    f (a+h)*:(g (a+h)-g a)+(f (a+h)-f a)*:g a.
  by rewrite scalerBr scalerBl addrA subrK.
rewrite hid; apply: le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
rewrite !(real_seminorm_scale hNY.1).
have hfirst : `|f (a+h)|*NY (g (a+h)-g a)<=(`|f a|+1)* p.
  exact: ler_pM (normr_ge0 _) (real_seminorm_nonnegative hNY.1 _)
    hvalue (ltW hdg).
have hsecond : `|f (a+h)-f a|*NY (g a)<=p*NY (g a).
  exact (ler_wpM2r hga (ltW hdf)).
have hlast := ler_wpM2r (ltW hK) hpe.
rewrite divfK ?gt_eqF // in hlast.
rewrite /K in hlast; nra.
Qed.

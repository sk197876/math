(** Federer (1969), 3.1.11, pp. 220–222:
    the first-order scalar-times-vector product rule,
    supporting the Taylor integration-by-parts calculation
    and the higher Leibniz rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormHigherCurveDerivativeUP
  NormedPrimitiveCell.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_vector_product_remainder]:
    the exact product remainder used in the Leibniz
    calculus of Federer 3.1.11, pp. 220–222.
    This is an algebraic supporting identity. *)
Lemma scalar_vector_product_remainder (R : realType) (Y : lmodType R)
    (u c l : R) (v w m : Y) :
  u*:v-c*:w-(l*:w+c*:m)=
    u*:(v-w-m)+(u-c-l)*:w+(u-c)*:m.
Proof.
have h1 : u*:v-c*:w=u*:(v-w)+(u-c)*:w.
  by rewrite scalerBr scalerBl addrA subrK.
have h2 : u*:(v-w)-c*:m=u*:(v-w-m)+(u-c)*:m.
  by rewrite (scalerBr u (v-w) m) scalerBl addrA subrK.
rewrite h1 opprD [(- (l*:w))+(- (c*:m))]addrC addrACA h2 -scalerBl.
by rewrite addrAC.
Qed.

(** Source for [scalar_vector_product_linear_term]:
    the differential of f g applied to h is
    Df(h) g+f Dg(h), Federer 3.1.11,
    pp. 220–222, the first Leibniz rule. *)
Definition scalar_vector_product_linear_term (R : realType)
    (X Y : lmodType R) (c : R) (w : Y) (L : Hom X R^o)
    (M : Hom X Y) : Hom X Y :=
  hom_comp (scalar_coefficient_linear_map w) L+c*:M.

(** Source for [norm_differential_scalar_product]:
    the first-order scalar-times-vector product rule
    supporting Federer 3.1.11, pp. 220–222.
    Both factors have their given common domain;
    no completeness or finite-dimensional hypothesis
    is imposed on either normed space. *)
Theorem norm_differential_scalar_product (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->R) (g : X->Y) a
    (L : Hom X R^o) (M : Hom X Y) :
  has_norm_differential NX (fun t : R^o=>`|t|) A f a L ->
  has_norm_differential NX NY A g a M ->
  has_norm_differential NX NY A (fun x=>f x*:g x) a
    (scalar_vector_product_linear_term (f a) (g a) L M).
Proof.
move=> hf hg; split; first exact: norm_differential_interior hf.
- rewrite /scalar_vector_product_linear_term.
  apply: (norm_bounded_linear_add hNY).
  + exact (norm_bounded_linear_compose (norm_differential_bounded hf)
      (scalar_coefficient_linear_bound hNY (g a))).
  + exact (norm_bounded_linear_scale hNY (f a) (norm_differential_bounded hg)).
- move=> e he.
  have [C [hC [r [hr hinc]]]] :=
    norm_differential_increment_bound (@scalar_absolute_value_norm R) hf.
  have [B [hB hM]] := norm_differential_bounded hg.
  pose K := `|f a|+C+NY (g a)+C*B+1.
  have hnfa := normr_ge0 (f a).
  have hnga := real_seminorm_nonnegative hNY.1 (g a).
  have hCB : 0<=C*B := mulr_ge0 (ltW hC) hB.
  have hK : 0<K by rewrite /K; lra.
  pose p := e/K.
  have hp : 0<p by rewrite /p divr_gt0.
  have [df [hdf hrf]] := norm_differential_remainder hf hp.
  have [dg [hdg hrg]] := norm_differential_remainder hg hp.
  exists (Num.min 1 (Num.min p (Num.min r (Num.min df dg)))).
  split; first by rewrite !lt_min ltr01 hp hr hdf hdg.
  move=> h ha hh.
  move: hh; rewrite !lt_min=>/andP [hh1 /andP [hhp /andP [hhr /andP [hhf hhg]]]].
  have hn := real_seminorm_nonnegative hNX.1 h.
  have hincf := hinc h ha hhr.
  have hvalue : `|f (a+h)|<=`|f a|+C.
    have htri : `|f (a+h)|<=`|f a|+`|f (a+h)-f a|.
      have ht := ler_normD (f a) (f (a+h)-f a).
      by rewrite addrC subrK in ht.
    apply: le_trans htri _; apply: lerD (lexx _) _.
    apply: le_trans hincf _.
    have ht := ler_wpM2l (ltW hC) (ltW hh1).
    by rewrite mulr1 in ht.
  have hfirst : NY (f (a+h)*:(g (a+h)-g a-M h))<=
      (`|f a|+C)*(p*NX h).
    rewrite (real_seminorm_scale hNY.1).
    exact: ler_pM (normr_ge0 _) (real_seminorm_nonnegative hNY.1 _)
      hvalue (hrg h ha hhg).
  have hsecond : NY ((f (a+h)-f a-L h)*:g a)<=
      (p*NX h)*NY (g a).
    rewrite (real_seminorm_scale hNY.1).
    exact (ler_wpM2r hnga (hrf h ha hhf)).
  have hthird : NY ((f (a+h)-f a)*:M h)<=C*B* p*NX h.
    rewrite (real_seminorm_scale hNY.1).
    apply: le_trans (ler_pM (normr_ge0 _) (real_seminorm_nonnegative hNY.1 _)
      hincf (hM h)) _.
    have hsq := ler_wpM2r hn (ltW hhp).
    have hscale := ler_wpM2l hCB hsq.
    nra.
  change (NY (f (a+h)*:g (a+h)-f a*:g a-
    (L h*:g a+f a*:M h))<=e*NX h).
  rewrite scalar_vector_product_remainder.
  apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD (le_trans (real_seminorm_triangle hNY.1 _ _)
    (lerD hfirst hsecond)) hthird) _.
  have hcoef : p*K=e by rewrite /p divfK // gt_eqF.
  have hnonneg : 0<=p*NX h := mulr_ge0 (ltW hp) hn.
  rewrite /K in hcoef; nra.
Qed.

(** Federer (1969), 3.1.1(2), p. 210: the differential of a composite is
    the composite of the differentials. The domain is the actual composite
    domain, not an assumed global inclusion of f(A) in the domain of g. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_composite_interior]: supporting domain
    step for Federer 3.1.1(2), p. 210. Differentiability of f and the
    interior-domain condition for g imply that g composed with f is
    defined on a neighbourhood of a. *)
Lemma norm_differential_composite_interior (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNY : is_real_norm NY) (A : X -> Prop) (B : Y -> Prop)
    (f : X -> Y) (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L ->
  norm_domain_interior NY B (f a) ->
  norm_domain_interior NX (fun x => A x /\ B (f x)) a.
Proof.
move=> hf [s [hs hB]].
have [r [hr hA]] := norm_differential_interior hf.
have [d [hd hcont]] := norm_differential_continuous_at hNY hf hs.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=> h hh.
have hmr : Num.min r d <= r by rewrite ge_min lexx.
have hmd : Num.min r d <= d by rewrite ge_min lexx orbT.
have ha := hA h (lt_le_trans hh hmr).
split=> //.
have hb := hB (f (a+h)-f a) (hcont h ha (lt_le_trans hh hmd)).
by rewrite addrC subrK in hb.
Qed.

(** Source for [norm_differential_chain]: Federer 3.1.1(2), p. 210.
    In words: if f is differentiable at a and g at f(a), their composite
    is differentiable at a with differential M composed with L. Neither
    completeness, finite dimension nor continuity of a derivative field
    is required. *)
Theorem norm_differential_chain (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> Z)
    (a : X) (L : Hom X Y) (M : Hom Y Z) :
  has_norm_differential NX NY A f a L ->
  has_norm_differential NY NZ B g (f a) M ->
  has_norm_differential NX NZ (fun x => A x /\ B (f x))
    (fun x => g (f x)) a (hom_comp M L).
Proof.
move=> hf hg; split.
- exact: (@norm_differential_composite_interior R X Y NX NY hNY A B f a L
    hf (norm_differential_interior hg)).
- exact: (@norm_bounded_linear_compose R X Y Z NX NY NZ L M
    (norm_differential_bounded hf) (norm_differential_bounded hg)).
- move=> e he.
  have [C [hC [r [hr hinc]]]] := norm_differential_increment_bound hNY hf.
  have [D [hD hM]] := norm_differential_bounded hg.
  have hden : 0 < C+D+1 by lra.
  pose p := e/(C+D+1).
  have hp : 0 < p by rewrite /p divr_gt0.
  have [df [hdf hrf]] := norm_differential_remainder hf hp.
  have [dg [hdg hrg]] := norm_differential_remainder hg hp.
  have hsmall : 0 < dg/C by rewrite divr_gt0.
  exists (Num.min df (Num.min r (dg/C))); split.
    by rewrite !lt_min hdf hr hsmall.
  move=> h [ha hb] hh.
  have hm1 : Num.min df (Num.min r (dg/C)) <= df by rewrite ge_min lexx.
  have hm2 : Num.min df (Num.min r (dg/C)) <= Num.min r (dg/C).
    by rewrite ge_min lexx orbT.
  have hm3 : Num.min r (dg/C) <= r by rewrite ge_min lexx.
  have hm4 : Num.min r (dg/C) <= dg/C by rewrite ge_min lexx orbT.
  have hhf := lt_le_trans hh hm1.
  have hhr := lt_le_trans (lt_le_trans hh hm2) hm3.
  have hhg := lt_le_trans (lt_le_trans hh hm2) hm4.
  pose k := f (a+h)-f a.
  have hk := hinc h ha hhr.
  have hkpos : NY k < dg.
    apply: le_lt_trans hk _.
    by move: hhg; rewrite ltr_pdivlMr // mulrC.
  have hshift : f a+k = f (a+h) by rewrite /k addrC subrK.
  have hbk : B (f a+k) by rewrite hshift.
  have hgr := hrg k hbk hkpos; rewrite hshift in hgr.
  have hfr := hrf h ha hhf.
  have hfirst : NZ (g (f (a+h))-g (f a)-M k) <= p*(C*NX h).
    apply: le_trans hgr _; apply: ler_wpM2l; first exact: ltW hp.
    exact hk.
  have hsecond : NZ (M (k-L h)) <= D*(p*NX h).
    apply: le_trans (hM (k-L h)) _.
    apply: ler_wpM2l=> //; exact hfr.
  have heq : g (f (a+h))-g (f a)-hom_comp M L h =
      (g (f (a+h))-g (f a)-M k)+M (k-L h).
    by rewrite hom_compE [M (k-L h)]linearB /= addrA subrK.
  rewrite heq; apply: le_trans (real_seminorm_triangle hNZ.1 _ _) _.
  apply: le_trans (lerD hfirst hsecond) _.
  have halg : p*(C*NX h)+D*(p*NX h) = (p*(C+D))*NX h by ring.
  rewrite halg; apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 h.
  have hcoef : p*(C+D) < p*(C+D+1) by rewrite ltr_pM2l // ltrDl.
  rewrite /p divfK ?gt_eqF // in hcoef.
  exact: ltW hcoef.
Qed.

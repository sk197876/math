(** Federer (1969), 3.1.1, pp. 209–210: differentiability is local on its
    domain and implies continuity. These supporting consequences prepare
    the chain rule without importing an external calculus library. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_domain_agreement]: supporting domain
    convention in Federer 3.1.1, p. 209. Changing a total representative
    outside A leaves the approximation unchanged. *)
Lemma norm_differential_domain_agreement (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (A : X -> Prop) (f g : X -> Y)
    (a : X) (L : Hom X Y) :
  (forall x, A x -> f x=g x) ->
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY A g a L.
Proof.
move=> hfg hf.
have ha := norm_domain_interior_member hNX (norm_differential_interior hf).
split; first exact: norm_differential_interior hf.
- exact: norm_differential_bounded hf.
- move=> e he; have [d [hd hrem]] := norm_differential_remainder hf he.
  exists d; split=> // h hh hs.
  rewrite -(hfg _ hh) -(hfg _ ha); exact: hrem.
Qed.

(** Source for [norm_differential_restrict]: supporting restriction law
    for the local domain in Federer 3.1.1, p. 209. The smaller domain
    must still contain a neighbourhood of the point. *)
Lemma norm_differential_restrict (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (A B : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) :
  (forall x, B x -> A x) -> norm_domain_interior NX B a ->
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY B f a L.
Proof.
move=> hBA hB hf; split=> //; first exact: norm_differential_bounded hf.
move=> e he; have [d [hd hrem]] := norm_differential_remainder hf he.
exists d; split=> // h hh hs; exact: hrem (hBA _ hh) hs.
Qed.

(** Source for [norm_differential_increment_bound]: supporting local
    growth estimate for Federer 3.1.1, p. 209, before the operator-norm
    limsup equality. A finite positive bound follows from the differential
    and the remainder with epsilon one. This is a pointwise bound at a,
    not a Lipschitz assertion between all nearby pairs. *)
Lemma norm_differential_increment_bound (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L ->
  exists C : R, 0 < C /\ exists d : R, 0 < d /\
    forall h, A (a+h) -> NX h < d -> NY (f (a+h)-f a) <= C*NX h.
Proof.
move=> hf; have [C [hC hL]] := norm_differential_bounded hf.
have [d [hd hrem]] := norm_differential_remainder hf ltr01.
exists (1+C); split; first by lra.
exists d; split=> // h hh hs.
have heq : f (a+h)-f a = (f (a+h)-f a-L h)+L h by rewrite subrK.
rewrite heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
have hb := lerD (hrem h hh hs) (hL h).
by rewrite -mulrDl in hb.
Qed.

(** Source for [norm_differential_continuous_at]: supporting continuity
    implied by differentiability in Federer 3.1.1, pp. 209–210. The
    conclusion is the epsilon definition on the function's domain. *)
Theorem norm_differential_continuous_at (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L -> forall e : R, 0 < e ->
    exists d : R, 0 < d /\ forall h, A (a+h) -> NX h < d ->
      NY (f (a+h)-f a) < e.
Proof.
move=> hf e he.
have [C [hC [r [hr hbound]]]] := norm_differential_increment_bound hNY hf.
have heC : 0 < e/C by rewrite divr_gt0.
exists (Num.min r (e/C)); split; first by rewrite lt_min hr heC.
move=> h hh hs.
have hmr : Num.min r (e/C) <= r by rewrite ge_min lexx.
have hme : Num.min r (e/C) <= e/C by rewrite ge_min lexx orbT.
have hsr : NX h < r := lt_le_trans hs hmr.
have hse : NX h < e/C := lt_le_trans hs hme.
apply: le_lt_trans (hbound h hh hsr) _.
by move: hse; rewrite ltr_pdivlMr // mulrC.
Qed.

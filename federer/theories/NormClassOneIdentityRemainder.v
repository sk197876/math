(** Federer (1969), 3.1.1, p. 210: when Df(0) is the identity,
    continuity of Df makes f-identity a strict contraction on a small ball.
    The proof uses the book's cited convex-domain bound from 2.2.7. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom RealNormUP InnerConvex NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialSubtraction
  NormClassOneUP NormDifferentialConvexBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_identity_remainder]: the choice of
    delta and the first Lipschitz estimate for g=f-identity in Federer
    3.1.1, p. 210. Any prescribed positive bound c is achieved on a
    sufficiently small closed ball contained in the actual domain. *)
Theorem norm_class_one_identity_remainder (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (A : X -> Prop)
    (f : X -> X) (D : X -> Hom X X) :
  is_norm_class_one_field N N A f D -> A 0 ->
  (forall v, D 0 v = v) -> forall c : R, 0 < c ->
  exists r : R, 0 < r /\ (forall x, N x <= r -> A x) /\
    forall x z, N x <= r -> N z <= r -> N ((f x-x)-(f z-z)) <= c*N (x-z).
Proof.
move=> hf hA0 hD0 c hc.
have [s [hs hAs]] := norm_differential_interior (norm_class_one_differential hf hA0).
have [d [hd hDd]] := norm_class_one_continuity hf hA0 hc.
pose r := Num.min s d / 2.
have hmin : 0 < Num.min s d by rewrite lt_min hs hd.
have hr : 0 < r by rewrite /r divr_gt0 // ltr0n.
have hhalf : r < Num.min s d by rewrite /r; lra.
have hms : Num.min s d <= s by rewrite ge_min lexx.
have hmd : Num.min s d <= d by rewrite ge_min lexx orbT.
have hAr : forall x, N x <= r -> A x.
  move=> x hx; have hh := hAs x (le_lt_trans hx (lt_le_trans hhalf hms)).
  by rewrite add0r in hh.
exists r; split=> //; split=> //.
have hconv : is_inner_convex (fun x => N x <= r).
  move=> x z hx hz t ht ht1.
  have h1t : 0 <= 1-t by rewrite subr_ge0.
  apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  rewrite !(real_seminorm_scale hN.1) (ger0_norm h1t) (ger0_norm ht).
  have hh := lerD (ler_wpM2l h1t hx) (ler_wpM2l ht hz); by nra.
apply: (@norm_differential_convex_bound R X X N N hN hN A
  (fun x => N x <= r) (fun x => f x-x) c hconv (ltW hc))=> x hx.
exists (D x-D 0); split.
- have hi : has_norm_differential N N A (D 0) x (D 0).
    apply: (norm_differential_linear hN hN (norm_differential_interior
      (norm_class_one_differential hf (hAr x hx)))).
    exists 1; split; first exact: ler01.
    by move=> v; rewrite hD0 mul1r.
  have hg := norm_differential_subtract hN hN
    (norm_class_one_differential hf (hAr x hx)) hi.
  apply: (@norm_differential_domain_agreement R X X N N hN A
    (fun z => f z-D 0 z) (fun z => f z-z) x (D x-D 0) _ hg)=> z _.
  by rewrite hD0.
- have hxa : A (0+x) by rewrite add0r; exact: hAr x hx.
  have hh := hDd x hxa (le_lt_trans hx (lt_le_trans hhalf hmd)).
  by rewrite add0r in hh.
Qed.

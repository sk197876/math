(** Federer (1969), 3.1.1, p. 210: the general inverse-function
    argument, reduced by translations and the inverse differential to
    the proved normalized iteration theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneNormalization
  NormClassOneNormalizedInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_inverse_ball]: the neighbourhoods
    in the inverse-function theorem of Federer 3.1.1, p. 210. A closed
    source ball lies in the domain, f is injective there with a uniform
    inverse Lipschitz bound, and its image contains a target ball of
    positive radius. Completeness is required only of the source. *)
Theorem norm_class_one_inverse_ball (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A : X -> Prop) (f : X -> Y) (D : X -> Hom X Y)
    (a : X) (M : Hom Y X) :
  is_norm_class_one_field NX NY A f D -> A a ->
  norm_bounded_linear NY NX M ->
  (forall v, M (D a v) = v) -> (forall w, D a (M w) = w) ->
  exists r s K : R, 0 < r /\ 0 < s /\ 0 < K /\
    (forall x, NX (x-a) <= r -> A x) /\
    (forall x z, NX (x-a) <= r -> NX (z-a) <= r ->
      NX (x-z) <= K*NY (f x-f z)) /\
    (forall x z, NX (x-a) <= r -> NX (z-a) <= r -> f x=f z -> x=z) /\
    (forall y, NY (y-f a) <= s -> exists x, NX (x-a) <= r /\ f x=y).
Proof.
move=> hf ha hM hML hLM.
pose F := fun u => M (f (a+u)-f a).
pose E := fun u => hom_comp M (D (a+u)).
have hF : is_norm_class_one_field NX NX (fun u => A (a+u)) F E :=
  @norm_class_one_normalization R X Y X NX NY NX hNX hNX A f D a (f a) M hf hM.
have hA0 : A (a+0) by rewrite addr0.
have hF0 : F 0 = 0 by rewrite /F addr0 subrr linear0.
have hE0 : forall v, E 0 v = v by move=> v; rewrite /E hom_compE addr0 hML.
have hc : 0 < (1/2:R) < 1 by apply/andP; split; lra.
have [r [hr [hAr [hlower [hinj hsurj]]]]] :=
  @norm_class_one_normalized_inverse R X NX hNX hcomplete
    (fun u => A (a+u)) F E hF hA0 hF0 hE0 (1/2) hc.
have [C [hC hMC]] := hM.
pose Q := C+1.
have hQ : 0 < Q by rewrite /Q; lra.
have hMQ : forall w, NX (M w) <= Q*NY w.
  move=> w; apply: le_trans (hMC w) _.
  apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNY.1 w.
  rewrite /Q; lra.
pose s := r/(2*Q).
have hs : 0 < s by rewrite /s divr_gt0 // mulr_gt0 // ltr0n.
have hK : 0 < 2*Q by rewrite mulr_gt0 // ltr0n.
exists r, s, (2*Q); split=> //; split=> //; split=> //; split.
- move=> x hx; have hh := hAr (x-a) hx; by rewrite addrC subrK in hh.
- have hFx : forall x, F (x-a) = M (f x-f a).
    by move=> x; rewrite /F [a+(x-a)]addrC subrK.
  have hdiff : forall x z, (x-a)-(z-a)=x-z.
    by move=> x z; rewrite opprB addrA subrK.
  split.
  + move=> x z hx hz.
    have hb := hlower (x-a) (z-a) hx hz.
    rewrite hdiff !hFx -linearB opprB addrA subrK in hb.
    have hh := le_trans hb (hMQ (f x-f z)); by nra.
  + split.
    * move=> x z hx hz heq.
      have hh : F (x-a)=F (z-a) by rewrite !hFx heq.
      have he := hinj (x-a) (z-a) hx hz hh.
      exact: (addIr (-a) he).
    * move=> y hy.
      have hsmall : NX (M (y-f a)) <= (1-1/2)*r.
        apply: le_trans (hMQ _) _.
        have hh := ler_wpM2l (ltW hQ) hy.
        have hseq : s*(2*Q)=r by rewrite /s divfK // gt_eqF.
        by nra.
      have [u [hu hFu]] := hsurj _ hsmall.
      exists (a+u); split; first by rewrite addrAC subrr add0r.
      have he : f (a+u)-f a = y-f a.
        move: (congr1 (D a) hFu); by rewrite /F !hLM.
      exact: (addIr (-f a) he).
Qed.

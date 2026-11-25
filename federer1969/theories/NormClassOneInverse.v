(** Federer (1969), 3.1.1, p. 210: the inverse of a univalent
    class-one map with invertible differentials is class one. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormDifferentialInverse NormClassOneUP
  NormClassOneInverseContinuity NormInverseFieldContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_inverse_field]: the last paragraph
    of Federer 3.1.1, p. 210. On the image domain of a univalent map,
    the inverse is class one and its differential at y is the inverse
    of Df at g(y). Completeness is retained from the preceding
    inverse-function theorem; no inverse continuity is assumed. *)
Theorem norm_class_one_inverse_field (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> X)
    (D : X -> Hom X Y) (E : X -> Hom Y X) :
  is_norm_class_one_field NX NY A f D ->
  (forall x, A x -> norm_bounded_linear NY NX (E x)) ->
  (forall x, A x -> forall v, E x (D x v)=v) ->
  (forall x, A x -> forall w, D x (E x w)=w) ->
  (forall x, A x -> B (f x) /\ g (f x)=x) ->
  (forall y, B y -> A (g y) /\ f (g y)=y) ->
  is_norm_class_one_field NY NX B g (fun y => E (g y)).
Proof.
move=> hf hE hED hDE hgf hfg.
have hg0 := @norm_class_one_inverse_class_zero R X Y NX NY hNX hNY hcomplete
  A B f g D E hf hE hED hDE hgf hfg.
constructor=> //.
- move=> b hb; have [ha hfa] := hfg b hb.
  have hdi : has_norm_differential NY NX B g (f (g b)) (E (g b)).
    apply: (@norm_differential_inverse R X Y NX NY hNX hNY A B f g
      (g b) (D (g b)) (E (g b))
      (norm_class_one_differential hf ha) (hE _ ha) (hED _ ha)).
    * rewrite hfa; exact: (hg0 b hb).1.
    * by rewrite hfa.
    * exact hfg.
    * move=> r hr; rewrite hfa; exact: (hg0 b hb).2 r hr.
  by rewrite hfa in hdi.
- move=> b hb e he; have [ha hfa] := hfg b hb.
  have [r [hr hEc]] := @norm_inverse_field_continuous R X Y NX NY hNX hNY A D E
    (norm_class_one_continuity hf) hE hED hDE (g b) ha e he.
  have [d [hd hgc]] := (hg0 b hb).2 r hr.
  exists d; split=> // k hk hs w.
  have hshift : g b+(g (b+k)-g b)=g (b+k) by rewrite addrC subrK.
  have hA : A (g b+(g (b+k)-g b)) by rewrite hshift; exact: (hfg _ hk).1.
  have hh := hEc (g (b+k)-g b) hA (hgc k hk hs) w.
  by rewrite hshift in hh.
Qed.

(** Source for [norm_class_one_inverse]: existence-of-field form
    of the class-one inverse conclusion in Federer 3.1.1, p. 210. *)
Corollary norm_class_one_inverse (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> X)
    (D : X -> Hom X Y) (E : X -> Hom Y X) :
  is_norm_class_one_field NX NY A f D ->
  (forall x, A x -> norm_bounded_linear NY NX (E x)) ->
  (forall x, A x -> forall v, E x (D x v)=v) ->
  (forall x, A x -> forall w, D x (E x w)=w) ->
  (forall x, A x -> B (f x) /\ g (f x)=x) ->
  (forall y, B y -> A (g y) /\ f (g y)=y) ->
  norm_class_one NY NX B g.
Proof.
move=> hf hE hED hDE hgf hfg; exists (fun y => E (g y)).
exact: (@norm_class_one_inverse_field R X Y NX NY hNX hNY hcomplete
  A B f g D E hf hE hED hDE hgf hfg).
Qed.

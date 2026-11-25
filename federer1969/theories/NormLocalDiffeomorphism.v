(** Federer (1969), 3.1.18, p. 229: the inverse-function step for
    the source chart. A genuine open ball and its actual image are
    obtained from the quantitative theorem of 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneInverseBall NormRegularity
  NormRegularityOperations NormClassOneRestriction NormOpenDomainLaws
  NormDiffeomorphismUP NormInjectiveDiffeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_local_diffeomorphism_from_inverse_field]: the
    neighbourhood U on which the source chart is a class-k
    diffeomorphism in Federer 3.1.18, p. 229. The supplied linear
    inverse field is bounded pointwise; its continuity is derived by
    the inverse-function theorem, not required here. *)
Theorem norm_local_diffeomorphism_from_inverse_field (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNX))
    (A:set X) (f:X->X) (D E:X->Hom X X) a k :
  norm_class hNX hNX A f k -> is_norm_class_one_field NX NX A f D -> A a ->
  (forall x, A x -> norm_bounded_linear NX NX (E x)) ->
  (forall x, A x -> cancel (D x) (E x)) ->
  (forall x, A x -> cancel (E x) (D x)) ->
  exists r:R, 0<r /\
    (forall x, NX (x-a)<r -> A x) /\
    exists g:X->X, is_norm_diffeomorphism hNX hNX
      (fun x=>NX (x-a)<r) (f @` [set x|NX (x-a)<r]) f g k.
Proof.
move=>hf hD ha hE hED hDE.
have [r [s [K [hr [hs [hK [hAr [hbound [hinj hsurj]]]]]]]]] :=
  @norm_class_one_inverse_ball R X X NX NX hNX hNX hcomplete A f D a (E a)
    hD ha (hE a ha) (hED a ha) (hDE a ha).
pose U:=fun x=>NX (x-a)<r.
have hUA x (hx:U x) : A x := hAr x (ltW hx).
have hopen x (hx:U x) : norm_domain_interior NX U x.
  exact (@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hfU := @norm_class_open_restriction R X X NX NX hNX hNX A U f k hUA hopen hf.
have hDU := @norm_class_one_field_open_restriction R X X NX NX A U f D hUA hopen hD.
have hEU x (hx:U x) := hE x (hUA x hx).
have hEDU x (hx:U x) := hED x (hUA x hx).
have hDEU x (hx:U x) := hDE x (hUA x hx).
have hiU x y (hx:U x) (hy:U y) : f x=f y -> x=y.
  exact: hinj x y (ltW hx) (ltW hy).
have [g hg] := @norm_injective_diffeomorphism_exists R X NX hNX hcomplete
  U f D E k hfU hDU hEU hEDU hDEU hiU.
exists r; split=>//; split; first exact hUA.
by exists g.
Qed.

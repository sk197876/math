(** Federer (1969), 3.1.22, p. 235: a differentiable
    map vanishing on S near a has zero differential on Tan(S,a). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormLinearDomainLaws
  NormDifferentialLocal NormDifferentialSubtraction TangentConeUP TangentConeBasic TangentDifferentialImage TangentSingleton.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_vanishing_tangent]: the opening
    observation of Federer 3.1.22, p. 235. A closure
    point a and a differentiable function vanishing on S in
    its neighbourhood satisfy h(a)=0 and Dh(a)v=0 for
    every tangent vector. The actual ambient domain is explicit. *)
Theorem norm_differential_vanishing_tangent (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (h:X->Y) a (L:Hom X Y) :
  has_norm_differential NX NY A h a L ->
  @closure (real_norm_metric_space hNX) S a ->
  (forall x,S x -> A x -> h x=0) ->
  h a=0 /\ forall v,norm_tangent_cone NX S a v -> L v=0.
Proof.
move=>hd hcl hz.
pose YN:=real_norm_metric_space hNY.
have hsub:(h @` (S `&` A)) `<=` [set 0].
  move=>y [x [hxS hxA] <-]; exact: hz x hxS hxA.
have hv0:=(@norm_tangent_zero_closure R X NX hNX S a).2 hcl.
have himg0:=@norm_differential_tangent_image R X Y NX NY hNX hNY A S h a L hd 0 hv0.
rewrite linear0 in himg0.
have hc0:=@norm_tangent_base_closure R Y NY hNY (h @` (S `&` A)) (h a) 0 himg0.
have hpoint:@closed YN [set 0].
  exact (@compact_closed YN _ (@metric_hausdorff R YN) (@compact_set1 YN 0)).
have hzero:h a=0:=hpoint (h a) (@closureS YN _ _ hsub (h a) hc0).
split=>// v hv.
have himg:=@norm_differential_tangent_image R X Y NX NY hNX hNY A S h a L hd v hv.
have ht:=@norm_tangent_mono R Y NY (h @` (S `&` A)) [set 0] (h a) hsub (L v) himg.
rewrite hzero (@norm_tangent_singleton R Y NY hNY 0) in ht.
exact ht.
Qed.

(** Source for [norm_differentials_agree_on_tangent]: the
    uniqueness argument preceding the definition of relative
    differentiation in Federer 3.1.22, p. 235.
    Locally agreeing differentiable extensions have the same
    differential on the tangent cone, though their ambient
    differentials can differ outside that cone. *)
Theorem norm_differentials_agree_on_tangent (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B S:set X) (f g:X->Y) a (L M:Hom X Y) :
  has_norm_differential NX NY A f a L -> has_norm_differential NX NY B g a M ->
  @closure (real_norm_metric_space hNX) S a ->
  (forall x,S x -> A x -> B x -> f x=g x) ->
  forall v,norm_tangent_cone NX S a v -> L v=M v.
Proof.
move=>hf hg hcl heq v hv.
pose U:=A `&` B.
have hU:norm_domain_interior NX U a.
  exact (@norm_domain_intersection_interior R X NX A B a
    (norm_differential_interior hf) (norm_differential_interior hg)).
have hfr:=@norm_differential_restrict R X Y NX NY A U f a L (fun _ h=>h.1) hU hf.
have hgr:=@norm_differential_restrict R X Y NX NY B U g a M (fun _ h=>h.2) hU hg.
have hdiff:=@norm_differential_subtract R X Y NX NY hNX hNY U f g a L M hfr hgr.
have hz x (hxS:S x) (hxU:U x):f x-g x=0 by rewrite (heq x hxS hxU.1 hxU.2) subrr.
have hh:=(@norm_differential_vanishing_tangent R X Y NX NY hNX hNY U S
  (fun x=>f x-g x) a (L-M) hdiff hcl hz).2 v hv.
change (L v-M v=0) in hh.
apply/eqP; by rewrite -subr_eq0 hh eqxx.
Qed.

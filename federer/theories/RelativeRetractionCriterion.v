(** Federer (1969), 3.1.22, pp. 235–236: relative
    differentiation can be tested by composing with any local retraction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormDifferentialChain NormDifferentialEnlarge NormClassOneUP NormRegularity RetractionUP
  TangentConeUP PartialFunctionUP RelativeDifferentialUP RetractionTangentIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_retraction_differential_criterion]: conditions
    (1) and (2), and the universal version [2], in Federer
    3.1.22, pp. 235–236. For each actual class-one local
    retraction, the relative derivative is exactly the restriction
    of D(f composed with r) to the tangent cone. Existence of
    such retractions on submanifolds was proved in 3.1.19. *)
Theorem relative_retraction_differential_criterion (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B T:set X) (f:X->Y) (r:X->X) a (L:partial_function X Y) :
  B a -> B `<=` A -> norm_domain_interior NX T a ->
  is_norm_class_retraction hNX T (B `&` T) r 1%N ->
  (@has_relative_norm_differential R X Y NX NY hNX A B f a L <->
    exists M:Hom X Y,has_norm_differential NX NY T (fun x=>f (r x)) a M /\
      is_tangent_differential_restriction NX B a M L).
Proof.
move=>ha hBA hTa hr; have haT:=norm_domain_interior_member hNX hTa.
have hra:r a=a:=norm_retraction_fixed hr (conj ha haT).
split.
- move=>[hcl [U [g [D [hg [hfg hDL]]]]]].
  have [P hP]:=(norm_class_firstP hNX hNX T r).1 (norm_retraction_class hr).
  have hPr:=@norm_class_one_differential R X X NX NX T r P hP a haT.
  have hga:has_norm_differential NX NY U g (r a) D by rewrite hra.
  have hcomp:=norm_differential_chain hNX hNX hNY hPr hga.
  have heq x (hx:T x /\ U (r x)):g (r x)=f (r x).
    symmetry; exact (hfg (r x) (norm_retraction_range hr hx.1).1 hx.2).2.
  have hfc:=norm_differential_domain_agreement hNX heq hcomp.
  have hd:=@norm_differential_enlarge R X Y NX NY (fun x=>T x /\ U (r x)) T
    (fun x=>f (r x)) a (hom_comp D (P a)) (fun x hx=>hx.1) hfc.
  exists (hom_comp D (P a)); split; first exact hd.
  move=>v y; split=>hy.
  + have [hv he]:=(hDL v y).1 hy; split; first exact hv.
    rewrite hom_compE (@norm_retraction_differential_tangent R X NX hNX B T r a
      (P a) ha hPr (fun x hx ht=>norm_retraction_fixed hr (conj hx ht)) v hv).
    exact he.
  + have [hv he]:=hy; apply: (hDL v y).2; split=>//.
    move: he; rewrite hom_compE (@norm_retraction_differential_tangent R X NX hNX B T r a
      (P a) ha hPr (fun x hx ht=>norm_retraction_fixed hr (conj hx ht)) v hv).
    by [].
- move=>[M [hd hML]]; split; first exact: subset_closure ha.
  exists T,(fun x=>f (r x)),M; split=>//; split=>// x hx ht.
  split; first exact (hBA x hx).
  by rewrite (norm_retraction_fixed hr (conj hx ht)).
Qed.

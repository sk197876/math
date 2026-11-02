(** Federer (1969), 3.1.21, p. 234: diffeomorphisms
    carry tangent cones exactly to tangent cones of local images. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormDifferentialInverseIdentities NormRegularity NormDiffeomorphismUP
  TangentConeUP TangentConeLocal TangentEmbeddingUP TangentEmbeddingImage NormLinearLeftInverseBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_diffeomorphism_tangent_image]: the application
    to class-one diffeomorphisms in Federer 3.1.21, p. 234.
    The ambient domain restriction is explicit and does not alter
    the original source tangent cone. All linear inverse and
    inverse-continuity hypotheses are proved from the chart laws. *)
Theorem norm_diffeomorphism_tangent_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A C:set X) (F:set Y) (f:X->Y) (g:Y->X) k a (L:Hom X Y) :
  (1<=k)%N -> is_norm_diffeomorphism hNX hNY A F f g k -> A a ->
  has_norm_differential NX NY A f a L ->
  L @` norm_tangent_cone NX C a=norm_tangent_cone NY (f @` (C `&` A)) (f a).
Proof.
move=>hk hD ha hf.
have hfa:=@norm_diffeomorphism_maps R X Y NX NY hNX hNY A F f g k hD a ha.
have hgf x (hx:A x):g (f x)=x:=@norm_diffeomorphism_left_inverse R X Y NX NY hNX hNY A F f g k hD x hx.
have hfg y (hy:F y):f (g y)=y:=@norm_diffeomorphism_right_inverse R X Y NX NY hNX hNY A F f g k hD y hy.
have hmap x (hx:A x):F (f x):=@norm_diffeomorphism_maps R X Y NX NY hNX hNY A F f g k hD x hx.
have himap y (hy:F y):A (g y):=@norm_diffeomorphism_inverse_maps R X Y NX NY hNX hNY A F f g k hD y hy.
have hgk:=norm_diffeomorphism_inverse_class hD.
have [E hE]:=(@norm_class_firstP R Y X NY NX hNY hNX F g).1 (norm_class_lower hk hgk).
pose M:=E (f a).
have hg:has_norm_differential NY NX F g (f a) M:=norm_class_one_differential hE hfa.
have hML:=@norm_differentials_left_inverse R X Y NX NY hNX hNY A F f g a L M hmap hgf hf hg.
have hLM:hom_comp L M=hom_of_linear (linear_id Y).
  have hff:has_norm_differential NX NY A f (g (f a)) L by rewrite hgf.
  exact (@norm_differentials_left_inverse R Y X NY NX hNY hNX F A g f (f a) M L himap hfg hg hff).
have hleft:cancel L M by move=>v; exact (congr1 (fun H:Hom X X=>H v) hML).
have hright:cancel M L by move=>v; exact (congr1 (fun H:Hom Y Y=>H v) hLM).
have hlower:=@norm_linear_left_inverse_lower_bound R X Y NX NY hNY L M
  (norm_differential_bounded hg) hleft.
have hclosed:=@norm_linear_right_inverse_closed_range R X Y NY hNY L M hright.
have hinv:norm_inverse_continuous_on_set NX NY (C `&` A) f a.
  move=>e he.
  have hc:=norm_class_continuous hgk.
  have [d [hd hb]]:=(hc (f a) hfa).2 e he.
  exists d; split=>// x [hx hAx] hfx.
  have hshift:f a+(f x-f a)=f x by rewrite addrC subrK.
  have hFx:F (f a+(f x-f a)) by rewrite hshift; exact: hmap x hAx.
  have hh:=hb (f x-f a) hFx hfx.
  by rewrite hshift (hgf x hAx) (hgf a ha) in hh.
have he:=@norm_tangent_embedding_image R X Y NX NY hNX hNY A (C `&` A) f a L
  hf hlower hclosed hinv.
rewrite (norm_tangent_open_restriction C (norm_differential_interior hf)) in he.
exact he.
Qed.

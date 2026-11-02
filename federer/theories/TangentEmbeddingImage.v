(** Federer (1969), 3.1.21, p. 234: equality of tangent
    images under the printed closed-range embedding hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormClosureBalls NormDifferentialUP
  TangentConeUP TangentConeBasic TangentDifferentialImage TangentEmbeddingUP
  TangentEmbeddingApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_embedding_image]: the equality
    Df(a)[Tan(S,a)]=Tan[f(S),f(a)] of Federer 3.1.21,
    p. 234. Inverse continuity is stated on the actual restricted
    image, and the linear homeomorphism is expressed by its
    positive lower bound and closed range; no target-wide inverse
    or completeness assumption is added. *)
Theorem norm_tangent_embedding_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a (L:Hom X Y) :
  has_norm_differential NX NY A f a L ->
  norm_linear_lower_bound NX NY L ->
  @closed (real_norm_metric_space hNY) (range L) ->
  norm_inverse_continuous_on_set NX NY S f a ->
  L @` norm_tangent_cone NX S a=norm_tangent_cone NY (f @` S) (f a).
Proof.
move=>hf [c [hc hlow]] hclosed hinv; apply/seteqP; split=>w.
- move=>[v hv <-].
  have hsub:(f @` (S `&` A)) `<=` (f @` S).
    move=>y [x [hx hAx] <-]; by exists x.
  exact (@norm_tangent_mono R Y NY (f @` (S `&` A)) (f @` S) (f a) hsub (L v)
    (@norm_differential_tangent_image R X Y NX NY hNX hNY A S f a L hf v hv)).
- move=>hw.
  have happrox:=@norm_tangent_embedding_approximation R X Y NX NY hNX hNY A S f a L c w
    hf hc hlow hinv hw.
  have hrange:range L w.
    apply: hclosed; apply: (@norm_closure_balls R Y NY hNY (range L) w).2=>d hd.
    have [x [r [hx [hr [hxa hxw]]]]]:=happrox 1 d ltr01 hd.
    exists (L (r*:(x-a))); split=>//; by exists (r*:(x-a)).
  have [v _ heq]:=hrange.
  exists v; last exact heq.
  move=>e he.
  have hce:0<c*e by rewrite mulr_gt0.
  have [x [r [hx [hr [hxa hxw]]]]]:=happrox e (c*e) he hce.
  have hh:=hlow (r*:(x-a)-v).
  rewrite (linB (hom_linear L)) heq in hh.
  exists x,r; split=>//; split=>//; split=>//.
  have hlt:=le_lt_trans hh hxw.
  by move: hlt; rewrite ltr_pM2l.
Qed.

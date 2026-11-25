(** Federer (1969), 3.1.21, p. 234: the affine
    coordinate fibres in the constant-rank normal form have
    tangent equal to the kernel of their linear coordinate map. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology TangentConeUP TangentClosedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_linear_fibre]: supporting
    Tan[f^-1{f(a)},a]=ker Df(a) in Federer 3.1.21,
    p. 234, for the affine coordinate fibre in 3.1.18.
    This linear special case holds in arbitrary normed spaces;
    boundedness proves the required closedness of the kernel. *)
Lemma norm_tangent_linear_fibre (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (L:Hom X Y) a : norm_bounded_linear NX NY L ->
  norm_tangent_cone NX [set x|L x=L a] a=[set v|L v=0].
Proof.
move=>hL.
have hzero:L 0=0:=linear0 L.
have hadd x y (hx:L x=0) (hy:L y=0):L (x+y)=0 by rewrite (linD (hom_linear L)) hx hy add0r.
have hscale c x (hx:L x=0):L (c*:x)=0 by rewrite (linZ (hom_linear L)) hx scaler0.
pose K:=@Subspace R X (fun x=>L x=0) hzero hadd hscale.
pose M:=real_norm_metric_space hNX.
pose V:=real_norm_metric_space hNY.
have hclosed:@closed M (K:set X).
  have hc:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY L hL.
  have h0:@closed V [set 0].
    exact (@compact_closed V _ (@metric_hausdorff R V) (@compact_set1 V 0)).
  change (@closed M ((fun x:M=>(L x:V)) @^-1` [set 0])).
  apply: preimage_closed; last exact h0.
  move=>x _; exact: hc x.
have htan:=@norm_tangent_closed_subspace R X NX hNX K 0 hclosed hzero.
have heq:norm_tangent_cone NX [set x|L x=L a] a=norm_tangent_cone NX K 0.
  apply/seteqP; split=>v hv e he.
  - have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
    exists (x-a),r; split.
    + change (L (x-a)=0); by rewrite (linB (hom_linear L)) hx subrr.
    + by rewrite subr0; split=>//; split.
  - have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
    exists (a+x),r; split.
    + change (L (a+x)=L a); by rewrite (linD (hom_linear L)) hx addr0.
    + rewrite addrAC subrr add0r.
      by move: hxa hxv; rewrite subr0=>hxa hxv; split=>//; split.
rewrite heq htan; by [].
Qed.

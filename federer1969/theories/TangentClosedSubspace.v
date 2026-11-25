(** Federer (1969), 3.1.21, p. 234: the tangent cone of a
    closed linear subspace at any of its points is that subspace. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import ModuleQuotient RealNormUP NormMetric NormClosureBalls TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_closed_subspace]: Tan(Z,z)=Z
    for a closed vector subspace Z and z in Z, explicitly used
    in Federer 3.1.21, p. 234. No finite-dimensional assumption
    is imposed; closedness is exactly the printed hypothesis. *)
Theorem norm_tangent_closed_subspace (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (Z:subspace X) a :
  @closed (real_norm_metric_space hN) Z -> Z a ->
  norm_tangent_cone N Z a=(Z:set X).
Proof.
move=>hclosed ha; apply/seteqP; split=>v.
- move=>hv; apply: hclosed; apply: (@norm_closure_balls R X N hN Z v).2=>e he.
  have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
  exists (r*:(x-a)); split=>//.
  exact (subspace_scale r (subspace_sub hx ha)).
- move=>hv e he.
  pose t:=e/(2*(N v+1)).
  have hnv:=real_seminorm_nonnegative hN.1 v.
  have ht:0<t by rewrite /t divr_gt0 // mulr_gt0 //; lra.
  have ht0:t!=0 by apply/eqP; lra.
  have htE:t*(2*(N v+1))=e by rewrite /t divfK //; apply/eqP; lra.
  exists (a+t*:v),t^-1; split.
  + exact (subspace_add ha (subspace_scale t hv)).
  + split; first by rewrite invr_gt0.
    rewrite addrAC subrr add0r scalerA mulVf // scale1r subrr (real_seminorm_zero hN.1).
    split; last exact he.
    rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW ht)); nra.
Qed.

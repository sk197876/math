(** Federer (1969), 3.1.21, p. 233: closure invariance and
    locality of the intrinsic tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra ring.
From Federer Require Import RealNormUP NormMetric NormClosureBalls TangentConeUP TangentConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Closure.
Variable R:realType.
Variable X:lmodType R.
Variable N:X->R.
Hypothesis hN:is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [norm_tangent_closure_invariant]: Tan(S,a)=
    Tan(Clos S,a), Federer 3.1.21, p. 233. Approximate each
    chosen closure point sufficiently accurately after its positive
    scaling factor has been fixed. *)
Lemma norm_tangent_closure_invariant S a :
  norm_tangent_cone N S a=norm_tangent_cone N (@closure M S) a.
Proof.
apply/seteqP; split=>v.
- exact (@norm_tangent_mono R X N S (@closure M S) a (@subset_closure M S) v).
- move=>hv e he.
  have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
  have [x [r [hx [hr [hxa hxv]]]]]:=hv (e/2) he2.
  pose d:=e/(2*(r+1)).
  have hd:0<d by rewrite /d divr_gt0 // mulr_gt0 //; lra.
  have [y [hy hyx]]:=(@norm_closure_balls R X N hN S x).1 hx d hd.
  have hrd:d*(2*(r+1))=e by rewrite /d divfK //; apply/eqP; lra.
  have hrd0:=real_seminorm_nonnegative hN.1 (y-x).
  have hxa0:=real_seminorm_nonnegative hN.1 (x-a).
  have hxv0:=real_seminorm_nonnegative hN.1 (r*:(x-a)-v).
  have hya:N (y-a)<=N (y-x)+N (x-a).
    have hh:=real_seminorm_triangle hN.1 (y-x) (x-a).
    by rewrite addrA subrK in hh.
  have heq:r*:(y-a)-v=r*:(y-x)+(r*:(x-a)-v).
    by rewrite addrA -scalerDr addrA subrK.
  have hbound:N (r*:(y-a)-v)<=r*N (y-x)+N (r*:(x-a)-v).
    rewrite heq; apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
    by rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW hr)).
  exists y,r; split=>//; split=>//; split; nra.
Qed.

(** Source for [norm_tangent_local_agreement]: supporting locality
    in the submanifold and fibre applications of Federer 3.1.21,
    p. 234. Agreement on one ambient ball gives identical cones. *)
Lemma norm_tangent_local_agreement S T a d : 0<d ->
  (forall x,N (x-a)<d -> (S x <-> T x)) ->
  norm_tangent_cone N S a=norm_tangent_cone N T a.
Proof.
move=>hd heq.
have hST (A B:set X):
    (forall x,N (x-a)<d -> A x -> B x) ->
    norm_tangent_cone N A a `<=` norm_tangent_cone N B a.
  move=>hAB v hv e he.
  have hmin:0<Num.min e d by rewrite lt_min he hd.
  have [x [r [hx [hr [hxa hxv]]]]]:=hv _ hmin.
  have hxe:N (x-a)<e:=lt_le_trans hxa (real_minimum_left_bound e d).
  have hxd:N (x-a)<d:=lt_le_trans hxa (real_minimum_right_bound e d).
  have hxve:N (r*:(x-a)-v)<e:=lt_le_trans hxv (real_minimum_left_bound e d).
  exists x,r; split; first exact: hAB x hxd hx.
  by split=>//; split.
apply/seteqP; split.
- apply: hST=>x hx; exact: (heq x hx).1.
- apply: hST=>x hx; exact: (heq x hx).2.
Qed.
End Closure.

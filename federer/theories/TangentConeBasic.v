(** Federer (1969), 3.1.21, p. 233: elementary tangent-cone
    laws, proved directly from the intrinsic epsilon definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_minimum_left_bound]: supporting choice of
    simultaneous epsilon tolerances for Federer 3.1.21, p. 233.
    The minimum is no larger than its first argument. *)
Lemma real_minimum_left_bound (R:realType) (e d:R) : Num.min e d<=e.
Proof. by rewrite ge_min lexx. Qed.

(** Source for [real_minimum_right_bound]: supporting choice of
    simultaneous epsilon tolerances for Federer 3.1.21, p. 233.
    The minimum is no larger than its second argument. *)
Lemma real_minimum_right_bound (R:realType) (e d:R) : Num.min e d<=d.
Proof. by rewrite ge_min lexx orbT. Qed.

Section Tangents.
Variable R:realType.
Variable X:lmodType R.
Variable N:X->R.
Hypothesis hN:is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [norm_tangent_two_radii]: supporting reformulation
    of the two strict inequalities in Federer 3.1.21, p. 233.
    Independent positive tolerances are equivalent to the printed
    common epsilon, by taking their minimum. *)
Lemma norm_tangent_two_radii S a v : norm_tangent_cone N S a v <->
  forall e d:R,0<e -> 0<d -> exists (x:X) (r:R),
    S x /\ 0<r /\ N (x-a)<e /\ N (r*:(x-a)-v)<d.
Proof.
split.
- move=>hv e d he hd.
  have hm:0<Num.min e d by rewrite lt_min he hd.
  have [x [r [hx [hr [hxa hxv]]]]]:=hv _ hm.
  exists x,r; split=>//; split=>//; split.
  + exact: lt_le_trans hxa (real_minimum_left_bound e d).
  + exact: lt_le_trans hxv (real_minimum_right_bound e d).
- move=>hrev eps hpos; exact (hrev eps eps hpos hpos).
Qed.

(** Source for [norm_tangent_mono]: supporting monotonicity
    for the closure and local-image assertions in Federer 3.1.21,
    pp. 233–234: inclusion of sets implies inclusion of cones. *)
Lemma norm_tangent_mono S T a : S `<=` T ->
  norm_tangent_cone N S a `<=` norm_tangent_cone N T a.
Proof.
move=>hST v hv e he; have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
exists x,r; split; first exact: hST hx.
by split=>//; split.
Qed.

(** Source for [norm_tangent_zero_closure]: the equivalence
    0 in Tan(S,a) iff a in Clos S, Federer 3.1.21, p. 233.
    The closure uses exactly the topology of the supplied norm. *)
Lemma norm_tangent_zero_closure S a :
  norm_tangent_cone N S a 0 <-> @closure M S a.
Proof.
split.
- move=>hv U hU.
  have [e he hb]:=proj1 (metricType_numDomainType.nbhs_mdistP (a:M) U) hU.
  have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
  exists x; split=>//; apply: hb.
  change (N (a-x)<e).
  by rewrite (real_seminorm_subtract hN.1).
- move=>hcl e he.
  have hn:nbhs (a:M) [set x|mdist (a:M) x<e].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a:M) _)).
    by exists e.
  have [x [hx hax]]:=hcl _ hn.
  have hxa:N (x-a)<e by rewrite (real_seminorm_subtract hN.1); exact hax.
  exists x,1; split=>//; split; first exact: ltr01.
  by rewrite scale1r subr0; split.
Qed.

(** Source for [norm_tangent_base_closure]: every nonempty
    tangent cone has its base point in Clos S; this supports the
    zero-scaling case of Federer 3.1.21, p. 233. *)
Lemma norm_tangent_base_closure S a v :
  norm_tangent_cone N S a v -> @closure M S a.
Proof.
move=>hv U hU.
have [e he hb]:=proj1 (metricType_numDomainType.nbhs_mdistP (a:M) U) hU.
have [x [r [hx [hr [hxa hxv]]]]]:=hv e he.
exists x; split=>//; apply: hb.
change (N (a-x)<e).
  by rewrite (real_seminorm_subtract hN.1).
Qed.

(** Source for [norm_tangent_nonnegative_scale]: v in Tan(S,a)
    and s>=0 imply s v in Tan(S,a), Federer 3.1.21, p. 233.
    The scalar zero is included using the closure equivalence. *)
Lemma norm_tangent_nonnegative_scale S a v s :
  norm_tangent_cone N S a v -> 0<=s -> norm_tangent_cone N S a (s*:v).
Proof.
move=>hv hs; case:(eqVneq s 0)=>[->|hs0].
- rewrite scale0r.
  exact ((@norm_tangent_zero_closure S a).2 (@norm_tangent_base_closure S a v hv)).
have hsp:0<s by rewrite lt_def hs0 hs.
move=>e he.
have hed:0<e/s by rewrite divr_gt0.
have [x [r [hx [hr [hxa hxv]]]]]:=(@norm_tangent_two_radii S a v).1 hv e (e/s) he hed.
exists x,(s*r); split=>//; split; first exact: mulr_gt0.
split=>//.
rewrite -scalerA -scalerBr (real_seminorm_scale hN.1) (ger0_norm hs).
move: hxv; by rewrite ltr_pdivlMr // mulrC.
Qed.

(** Source for [norm_tangent_cone_closed]: Tan(S,a) is closed,
    Federer 3.1.21, p. 233. Approximate a closure point by a
    tangent vector within epsilon/2 and use its defining witness. *)
Lemma norm_tangent_cone_closed S a : @closed M (norm_tangent_cone N S a).
Proof.
move=>v hcl e he.
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
have hn:nbhs (v:M) [set w|mdist (v:M) w<e/2].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (v:M) _)).
  by exists (e/2).
have [w [hw hvw]]:=hcl _ hn.
have [x [r [hx [hr [hxa hxw]]]]]:=hw (e/2) he2.
have hwe:N (w-v)<e/2 by rewrite (real_seminorm_subtract hN.1); exact hvw.
exists x,r; split=>//; split=>//; split; first by lra.
have ht:=real_seminorm_triangle hN.1 (r*:(x-a)-w) (w-v).
rewrite addrA subrK in ht; lra.
Qed.
End Tangents.

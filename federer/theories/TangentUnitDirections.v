(** Federer (1969), 3.1.21, p. 233: tangent unit vectors
    are the intersection of closures of the normalized secant directions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import RealNormUP RealNormNormalization NormMetric NormMetricContinuity
  NormClosureBalls TangentConeUP TangentConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_secant_directions]: the sets of vectors
    (x-a)/|x-a| with a!=x in S intersect U(a,e), in the
    displayed intersection of Federer 3.1.21, p. 233. *)
Definition norm_secant_directions (R:realType) (X:lmodType R)
    (N:X->R) (S:set X) a e : set X :=
  [set real_norm_normalize N (x-a)|x in [set x|S x /\ x!=a /\ N (x-a)<e]].

Section Directions.
Variable R:realType.
Variable X:lmodType R.
Variable N:X->R.
Hypothesis hN:is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [norm_normalized_approximation]: supporting
    normalization estimate for the unit-direction identity of
    Federer 3.1.21, p. 233. If |v|= 1 and r>0, the
    normalized nonzero vector differs from v by at most twice
    the error |r h-v|. *)
Lemma norm_normalized_approximation h v r :
  N v = 1 -> 0<r -> h!=0 ->
  N (real_norm_normalize N h-v)<=2*N (r*:h-v).
Proof.
move=>hv hr hh.
have hnh:0<N h by rewrite (real_norm_positive hN.1 hN.2).
have hn1:N (real_norm_normalize N h)= 1.
  by rewrite (real_norm_normalize_value hN.1) (gt_eqF hnh).
have heq:real_norm_normalize N h-r*:h=(1-r*N h)*:real_norm_normalize N h.
  rewrite scalerBl scale1r -scalerA (real_norm_normalize_reconstruct hN.2).
  by [].
have hnorm:N (real_norm_normalize N h-r*:h)=`|1-N (r*:h)|.
  by rewrite heq (real_seminorm_scale hN.1) hn1 mulr1
    (real_seminorm_scale hN.1) (ger0_norm (ltW hr)).
have hrev:=real_norm_change_bound hN v (r*:h).
rewrite hv (real_seminorm_subtract hN.1) in hrev.
have ht:=real_seminorm_triangle hN.1 (real_norm_normalize N h-r*:h) (r*:h-v).
rewrite addrA subrK hnorm in ht; lra.
Qed.

(** Source for [norm_tangent_unit_directions]: the displayed
    unit-vector formula in Federer 3.1.21, p. 233, pointwise
    at a unit vector. Every positive ambient radius is retained. *)
Theorem norm_tangent_unit_directions S a v : N v = 1 ->
  (norm_tangent_cone N S a v <-> forall e:R,0<e ->
    @closure M (norm_secant_directions N S a e) v).
Proof.
move=>hnv; split.
- move=>hv e he; apply: (@norm_closure_balls R X N hN _ v).2=>d hd.
  pose q:=Num.min (1/2) (d/4).
  have hq:0<q by rewrite /q lt_min !divr_gt0 // ltr0n.
  have [x [r [hx [hr [hxa hxv]]]]]:=(@norm_tangent_two_radii R X N S a v).1 hv e q he hq.
  have hxa0:x!=a.
    apply/negP=>/eqP hxa0; subst x.
    rewrite subrr scaler0 sub0r (real_seminorm_negate hN.1) hnv in hxv.
    have hq1:q<=1/2:=real_minimum_left_bound (1/2) (d/4); lra.
  have hh:(x-a)!=0 by rewrite subr_eq0.
  exists (real_norm_normalize N (x-a)); split.
  + exists x=>//; by split=>//; split.
  + have hb:=norm_normalized_approximation hnv hr hh.
    have hqd:q<=d/4:=real_minimum_right_bound (1/2) (d/4); lra.
- move=>hdir e he.
  have [w [hw hwv]]:=
    (@norm_closure_balls R X N hN _ v).1 (hdir e he) e he.
  have [x [hx [hxa hxe]] heq]:=hw; subst w.
  have hnx:0<N (x-a) by rewrite (real_norm_positive hN.1 hN.2) subr_eq0.
  exists x,(N (x-a))^-1; split=>//; split; first by rewrite invr_gt0.
  by split.
Qed.

(** Source for [norm_tangent_unit_intersection]: the exact set
    equation displayed in Federer 3.1.21, p. 233. Closure
    points of normalized directions still have norm one, so the
    right hand side needs no additional unit-sphere intersection. *)
Theorem norm_tangent_unit_intersection S a :
  norm_tangent_cone N S a `&` [set v|N v = 1]=
    \bigcap_(e in [set e:R|0<e]) @closure M (norm_secant_directions N S a e).
Proof.
apply/seteqP; split=>v.
- move=>[hv hn] e he; exact ((@norm_tangent_unit_directions S a v hn).1 hv e he).
- move=>hv.
  have hn:N v = 1.
    apply: contrapT=>hne.
    have hp:0<`|N v-1| by rewrite normr_gt0 subr_eq0; apply/eqP; exact hne.
    have [w [hw hwv]]:=
      (@norm_closure_balls R X N hN _ v).1 (hv 1 ltr01) _ hp.
    have [x [hx [hxa hxe]] heq]:=hw; subst w.
    have hnx:0<N (x-a) by rewrite (real_norm_positive hN.1 hN.2) subr_eq0.
    have hwn:N (real_norm_normalize N (x-a))= 1.
      by rewrite (real_norm_normalize_value hN.1) (gt_eqF hnx).
    have hh:=real_norm_change_bound hN v (real_norm_normalize N (x-a)).
    rewrite hwn (real_seminorm_subtract hN.1) in hh.
    have hbad:=le_lt_trans hh hwv; by rewrite ltxx in hbad.
  split=>//; exact ((@norm_tangent_unit_directions S a v hn).2 hv).
Qed.
End Directions.

(** Federer (1969), 3.2.16, pp. 252–253:
    directional cones are open and invariant under
    positive dilation about their base point. These
    facts justify the finite compact-direction cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws
  NormMetricScaleContinuity MetricClosedBalls MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_affine_increment_continuous]: the
    continuous dilation x to r(x-a) used for
    E(a,v,e), Federer 3.2.16, p. 252. *)
Lemma norm_affine_increment_continuous (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX) (a : X) (r : R) :
  continuous (fun x : real_norm_metric_space hNX =>
    (r *: (x-a) : real_norm_metric_space hNX)).
Proof.
pose M := real_norm_metric_space hNX.
have hShift : continuous (fun x : M => (x-a : M)).
  have he : (fun x : M => (x-a : M))=(fun x : M => (-a+x : M)).
    by apply: funext=> x; rewrite addrC.
  rewrite he; exact: real_norm_metric_translate_continuous.
move=> x; exact: continuous_comp (hShift x)
  (@real_norm_metric_scale_continuous R X NX hNX r (x-a)).
Qed.

(** Source for [approximate_direction_cone_open]: open
    directional cones in the finite-cover argument of
    Federer 3.2.16, p. 253. The union over
    positive dilations is an arbitrary open union. *)
Theorem approximate_direction_cone_open (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (a v : X) (e : R) :
  @open (real_norm_metric_space hNX) (approximate_direction_cone NX a v e).
Proof.
pose M := real_norm_metric_space hNX.
pose F (r : R) : M -> M := fun x => r *: (x-a).
pose B : set M := [set y | mdist (v : M) y<e].
have hEq : approximate_direction_cone NX a v e=
    \bigcup_(r in [set r : R | 0<r]) (F r @^-1` B).
  apply/seteqP; split=> x.
  - move=> [r [hr hx]]; exists r=> //.
    change (is_true (NX (v-r *: (x-a))<e)).
    by rewrite (real_seminorm_subtract hNX.1).
  - move=> [r hr hx]; exists r; split=> //.
    change (is_true (NX (v-r *: (x-a))<e)) in hx.
    by rewrite (real_seminorm_subtract hNX.1) in hx.
rewrite hEq; apply: bigcup_open=> r hr.
exact: (@continuousP M M (F r)).1
  (@norm_affine_increment_continuous R X NX hNX a r) B (metric_open_ball_open (v : M) e).
Qed.

(** Source for [approximate_direction_cone_center_direction]:
    a+v belongs to every positive-tolerance E(a,v,e),
    Federer 3.2.16, p. 253, compact-cover paragraph. *)
Lemma approximate_direction_cone_center_direction (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX) (a v : X) e :
  0<e -> approximate_direction_cone NX a v e (a+v).
Proof.
move=> he; exists 1; split; first exact: ltr01.
by rewrite addrAC subrr add0r scale1r subrr (real_seminorm_zero hNX.1).
Qed.

(** Source for [approximate_direction_cone_positive_ray]:
    the last sentence of the compact-cover argument
    in Federer 3.2.16, p. 253: the same
    finite directional cones cover all positive rays. *)
Lemma approximate_direction_cone_positive_ray (R : realType)
    (X : lmodType R) (NX : X -> R) (a v w : X) (e t : R) :
  0<t -> approximate_direction_cone NX a v e (a+w) ->
  approximate_direction_cone NX a v e (a+t *: w).
Proof.
move=> ht [r [hr hx]].
exists (r/t); split; first by rewrite divr_gt0.
rewrite addrAC subrr add0r scalerA divfK ?gt_eqF //.
by move: hx; rewrite addrAC subrr add0r.
Qed.

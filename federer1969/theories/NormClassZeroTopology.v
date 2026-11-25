(** Federer (1969), 3.1.1, pp. 210-211: class zero is continuity
    on an open domain. These adapters connect the intrinsic epsilon
    laws to the metric topology used in the Borel differential proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_domain_open]: the open-domain
    requirement for class zero in 3.1.1, p. 210, interpreted in
    the topology of the supplied norm. *)
Lemma norm_class_zero_domain_open (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (A : set X) (f : X -> Y) :
  norm_class_zero NX NY A f ->
  @open [the topologicalType of real_norm_metric_space hNX] A.
Proof.
move=> hf; rewrite openE=> a ha.
exact: (proj1 (@norm_domain_interior_neighbourhood R X NX hNX A a) (hf a ha).1).
Qed.

(** Source for [norm_class_zero_continuous_at]: the continuous
    representative at every point of the open domain in 3.1.1,
    pp. 210-211. Arbitrary values outside the domain are harmless
    because every domain point has a neighbourhood inside it. *)
Lemma norm_class_zero_continuous_at (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (f : X -> Y) (a : X) :
  norm_class_zero NX NY A f -> A a ->
  (fun x : real_norm_metric_space hNX => (f x : real_norm_metric_space hNY)) @ (a : real_norm_metric_space hNX) --> (f a : real_norm_metric_space hNY).
Proof.
move=> hf ha W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (f a : real_norm_metric_space hNY) W) hW.
have [r [hr hA]] := (hf a ha).1.
have [d [hd hb]] := (hf a ha).2 e he.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a : real_norm_metric_space hNX) _)).
exists (Num.min r d); first by rewrite /= lt_min hr hd.
move=> x hx; apply: hball.
change (is_true (NY (f a-f x) < e)).
have hsmall : NX (x-a) < Num.min r d.
  rewrite (real_seminorm_subtract hNX.1); exact hx.
have /andP [hxr hxd] : (NX (x-a)<r) && (NX (x-a)<d) by rewrite -lt_min.
have hAx := hA (x-a) hxr.
have hfx := hb (x-a) hAx hxd.
rewrite (addrC a (x-a)) subrK in hfx.
by rewrite (real_seminorm_subtract hNY.1).
Qed.

(** Source for [norm_class_zero_restriction_continuous]: the
    function on its actual domain, required for the Borel argument
    of 3.1.1, p. 211, is continuous in the metric subspace topology. *)
Lemma norm_class_zero_restriction_continuous (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (f : X -> Y) :
  norm_class_zero NX NY A f ->
  continuous (fun x : metric_subset (fun y : real_norm_metric_space hNX => A y) =>
    (f (val x) : real_norm_metric_space hNY)).
Proof.
move=> hf x W hW.
have hpre := @norm_class_zero_continuous_at R X Y NX NY hNX hNY A f
  (val x) hf (set_valP x) W hW.
exact: (@metric_subset_inclusion_continuous R (real_norm_metric_space hNX) A x _ hpre).
Qed.

(** Source for [norm_class_zero_local_control]: supporting
    neighbourhood form of class-zero continuity in 3.1.1,
    pp. 210-211. A small ambient ball stays in the actual
    domain and controls the change in the function value. *)
Lemma norm_class_zero_local_control (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (A : set X) (f : X -> Y) a e :
  norm_class_zero NX NY A f -> A a -> 0<e ->
  exists r : R, 0<r /\ forall b, NX (b-a)<r -> A b /\ NY (f b-f a)<e.
Proof.
move=> hf ha he.
have [r [hr hA]] := (hf a ha).1.
have [d [hd hb]] := (hf a ha).2 e he.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=> b; rewrite lt_min=> /andP [hbr hbd].
have hAb := hA (b-a) hbr; rewrite (addrC a (b-a)) subrK in hAb.
split=> //.
have hab : A (a+(b-a)) by rewrite (addrC a (b-a)) subrK.
have hfb := hb (b-a) hab hbd.
by rewrite (addrC a (b-a)) subrK in hfb.
Qed.

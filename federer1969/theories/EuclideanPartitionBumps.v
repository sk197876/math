(** Federer (1969), 3.1.13, pp. 224–225:
    the actual rescaled bump family attached to
    the selected balls. Its plateaus cover U,
    and its compact supports form a locally
    finite refinement of the original open cover. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness MetricClosedBalls EuclideanClosedBallCompact CompactSupportFunctionUP
  ContinuousMultilinearUP NormClassHigherUP NormUnitBumpUP NormUnitBumpSealed InnerSmoothUnitBump
  NormScaledUnitBump FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  EuclideanPartitionLocalFiniteness EuclideanPartitionOverlapNeighborhood
  LocallyFiniteFamilyUP NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_partition_bump]:
    the formula u_s(x)=mu((x-s)/(5h(s))),
    Federer 3.1.13, p. 224,
    using the sealed smooth radial cutoff. *)
Definition euclidean_partition_bump (R : realType) m
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (s x : inner_metric_space (@euclidean_inner_productP R m)) :=
  norm_scaled_unit_bump (inner_smooth_unit_bump (@euclidean_inner_productP R m))
    s (5*federer_cover_radius Phi s) x.

Section BumpFamily.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variables (Phi : set (set X)) (S : set X).
Hypothesis ho : forall T, Phi T -> open T.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).
Local Notation u := (euclidean_partition_bump Phi).

(** Source for [euclidean_partition_bump_radius_positive]:
    every selected radius 5h(s) is positive,
    Federer 3.1.13, p. 224. *)
Lemma euclidean_partition_bump_radius_positive s : S s -> 0<5*h s.
Proof.
move=>hs; apply: mulr_gt0; first by rewrite ltr0n.
apply: (federer_cover_radius_positive ho).
have [T hT hsT] := partition_ball_centers_in_domain hS hs; by exists T.
Qed.

(** Source for [euclidean_partition_bump_range]:
    0<=u_s<=1, Federer 3.1.13, p. 224. *)
Lemma euclidean_partition_bump_range s x : S s -> 0<=u s x<=1.
Proof.
move=>hs; exact: (norm_scaled_unit_bump_range
  (inner_smooth_unit_bump_laws (@euclidean_inner_productP R m)) s (5*h s) x).
Qed.

(** Source for [euclidean_partition_bump_plateau]:
    u_s equals one on B[s,5h(s)],
    Federer 3.1.13, p. 224. *)
Lemma euclidean_partition_bump_plateau s x :
  S s -> metric_closed_ball s (5*h s) x -> u s x= 1.
Proof.
move=>hs hx.
apply: (norm_scaled_unit_bump_inner hN
  (inner_smooth_unit_bump_laws (@euclidean_inner_productP R m))
  (euclidean_partition_bump_radius_positive hs)).
change (is_true (N (s-x)<=5*h s)) in hx.
by rewrite (real_seminorm_subtract hN.1).
Qed.

(** Source for [euclidean_partition_bump_zero_off_ball]:
    u_s vanishes off B[s,10h(s)],
    Federer 3.1.13, p. 224. *)
Lemma euclidean_partition_bump_zero_off_ball s x :
  S s -> ~metric_closed_ball s (10*h s) x -> u s x=0.
Proof.
move=>hs hn.
have hdist : 10*h s<mdist s x.
  rewrite ltNge; apply/negP; exact hn.
change (is_true (10*h s<N (s-x))) in hdist.
rewrite (real_seminorm_subtract hN.1) in hdist.
apply: (norm_scaled_unit_bump_outer hN
  (inner_smooth_unit_bump_laws (@euclidean_inner_productP R m))
  (euclidean_partition_bump_radius_positive hs)).
have he : 2*(5*h s)= 10*h s by ring.
rewrite he; exact: (ltW hdist).
Qed.

(** Source for [euclidean_partition_bump_support]:
    spt(u_s) is contained in B[s,10h(s)],
    Federer 3.1.13, p. 224. *)
Lemma euclidean_partition_bump_support s :
  S s -> real_function_support (u s) `<=` metric_closed_ball s (10*h s).
Proof.
move=>hs; apply: (real_function_support_in_closed_set (@metric_closed_ball_closed R _ s (10*h s))).
move=>x hx; exact: (euclidean_partition_bump_zero_off_ball hs hx).
Qed.

(** Source for [euclidean_partition_bump_compact_support]:
    each bump support is compact, as
    used for the refinement and global
    extension in Federer 3.1.13, pp. 224–225. *)
Lemma euclidean_partition_bump_compact_support s :
  S s -> compact (real_function_support (u s)).
Proof.
move=>hs; apply: (real_function_compact_support_in_closed_set
  (@euclidean_closed_metric_ball_compact R m s (10*h s)) (@metric_closed_ball_closed R _ s (10*h s))).
move=>x hx; exact: (euclidean_partition_bump_zero_off_ball hs hx).
Qed.

(** Source for [euclidean_partition_bump_plateaus_cover]:
    every x in U lies in a
    bump's unit plateau, Federer 3.1.13,
    pp. 224–225; consequently the sum is at least one. *)
Lemma euclidean_partition_bump_plateaus_cover x :
  U x -> exists s, S s /\ u s x= 1.
Proof.
move=>hx; rewrite -(partition_fivefold_balls_cover hS) in hx.
have [s hs hsx] := hx; exists s; split; first exact hs.
exact: (euclidean_partition_bump_plateau hs hsx).
Qed.

(** Source for [euclidean_partition_bump_locally_finite]:
    the actual bump family is locally finite
    on U, Federer 3.1.13, p. 225.
    The finite selection is exactly S_x. *)
Theorem euclidean_partition_bump_locally_finite :
  is_norm_locally_finite_function_family N U S u.
Proof.
move=>x hx.
have [hOx [hOU [hOo hmeet]]] := partition_overlap_neighborhood_laws S ho hx.
pose K := lipschitz_radius_overlap S h 10 10 x.
have hK : finite_set K := partition_ball_overlap_finite hS hx.
pose F := fset_set K.
have hFI s : s \in F -> S s.
  rewrite /F in_fset_set //; by move/set_mem=>[hs _].
exists (partition_overlap_neighborhood Phi x); split; first exact hOx.
split; first exact hOU; split; first exact hOo.
exists F; split; first exact hFI.
move=>y hy s hs hn; apply: (euclidean_partition_bump_zero_off_ball hs)=>hsy.
have hin : s \in F.
  rewrite /F in_fset_set //; apply/mem_set; exact: (hmeet s y hs hy hsy).
by move:hn; rewrite hin.
Qed.

(** Source for [euclidean_partition_bump_supports_refine]:
    the compact bump supports refine Phi
    and are locally finite on U,
    Federer 3.1.13, p. 225. *)
Theorem euclidean_partition_bump_supports_refine :
  (forall s, S s -> exists T, Phi T /\ real_function_support (u s) `<=` T) /\
  is_locally_finite_family_on U S (fun s=>real_function_support (u s)).
Proof.
split.
- move=>s hs; have [T [hT hKT]] := partition_tenfold_balls_subordinate hS hs.
  exists T; split; first exact hT.
  exact: (subset_trans (euclidean_partition_bump_support hs) hKT).
- exact: (partition_subordinate_supports_locally_finite ho hS
    (fun s hs=>euclidean_partition_bump_support hs)).
Qed.

(** Source for [euclidean_partition_bump_smooth]:
    all u_s have class infinity on R^m,
    Federer 3.1.13, p. 224. *)
Theorem euclidean_partition_bump_smooth
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space N
      (fun t : R^o=>`|t|) (@ev i) (@ZN i)) s :
  S s -> norm_class_infinity N (fun t : R^o=>`|t|) ev ZN (fun _=>True) (u s).
Proof.
move=>hs k; apply: (norm_scaled_unit_bump_smooth hN s (5*h s) hZ _ k).
move=>i; exact: (@NormUnitBump.smooth R (R_n R m) N (@euclidean_inner_product R m) hN
  (inner_product_squared_norm_specification (@euclidean_inner_productP R m)) Z ev ZN hZ i).
Qed.
End BumpFamily.

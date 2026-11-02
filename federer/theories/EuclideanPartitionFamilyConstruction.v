(** Private existence proof for the qualitative
    partition family in Federer (1969), 3.1.13,
    pp. 224–225. Existing sealed
    finite sums and zero extensions provide the
    witnesses; the public interface exposes their laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  MetricClosedBalls EuclideanClosedBallCompact CompactSupportFunctionUP
  ContinuousMultilinearUP NormClassHigherUP NormClassHigherRestriction
  NormLocallyFiniteFamilyUP FiniteFamilySumUP FiniteFamilySumSealed
  NormClassHigherLocallyFiniteSum FinitePositiveFamilyNormalization
  NormPartitionUnityUP NormPartitionUnityLaws NormPartitionNormalization SmoothZeroExtension
  FedererCoverRadius EuclideanPartitionBallCoverUP EuclideanPartitionOverlapNeighborhood
  EuclideanPartitionBumps EuclideanPartitionFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_partition_family_exists]:
    construction of sigma and the normalized
    globally smooth v_s, Federer 3.1.13,
    p. 225. The derivative
    estimates are separate obligations, not assumptions
    of this existence proof. *)
Theorem euclidean_partition_family_exists (R : realType) m
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (forall T, Phi T -> open T) ->
  is_federer_partition_ball_cover Phi S ->
  exists sigma v, is_euclidean_partition_family ev ZN Phi S sigma v.
Proof.
move=>ho hS.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose N := inner_norm (@euclidean_inner_productP R m).
have hN := inner_norm_real_norm (@euclidean_inner_productP R m).
pose U : set X := \bigcup_(T in Phi) T.
pose u := @euclidean_partition_bump R m Phi.
have hUo : open U by apply: bigcup_open=>T hT; exact: (ho T hT).
have hU := inner_open_norm_domain hUo.
have hlocal := euclidean_partition_bump_locally_finite ho hS.
have hfin := norm_locally_finite_active_family hlocal.
pose sigma := @FiniteFamilySum.value X X R^o U S u hfin.
have hsum : is_finite_family_sum_on U S u sigma := FiniteFamilySum.laws hfin.
have hnonneg s (hs : S s) x (_ : U x) : 0<=u s x.
  exact: (andP (euclidean_partition_bump_range Phi x hs)).1.
have hplateau x (hx : U x) : exists s, S s /\ u s x= 1.
  exact: (euclidean_partition_bump_plateaus_cover ho hS hx).
have hu s (hs : S s) : norm_class_infinity N (fun t : R^o=>`|t|) ev ZN U (u s).
  move=>k; apply: (norm_class_higher_open_restriction hN
    (@scalar_absolute_value_norm R) hZ (fun x (_ : U x)=>I) hU).
  exact: (euclidean_partition_bump_smooth Phi hZ hs k).
have hsmooth := norm_class_infinity_locally_finite_sum hN (@scalar_absolute_value_norm R)
  hZ hlocal hsum hu.
pose q s x := u s x/sigma x.
have hq : is_norm_smooth_partition_of_unity N ev ZN U S q.
  exact: (norm_partition_from_positive_bumps hN hZ hlocal hsum hnonneg hplateau hu).
pose v s := norm_zero_extended_function U (q s).
have hzero s (hs : S s) x (hx : ~metric_closed_ball s (10*federer_cover_radius Phi s) x) :
    v s x=0.
  case:(pselect (U x))=>[hux|hux].
  - rewrite /v norm_zero_extended_function_on // /q /u.
    by rewrite (euclidean_partition_bump_zero_off_ball ho hS hs hx) mul0r.
  - exact: (norm_zero_extended_function_off (q s) hux).
have hvsmooth s (hs : S s) :
    norm_class_infinity N (fun t : R^o=>`|t|) ev ZN (fun _=>True) (v s).
  pose K := metric_closed_ball s (10*federer_cover_radius Phi s).
  have hKc : @closed [the topologicalType of real_norm_metric_space hN] K.
    exact: (@metric_closed_ball_closed R (real_norm_metric_space hN) s
      (10*federer_cover_radius Phi s)).
  have [T [hT hKT]] := partition_tenfold_balls_subordinate hS hs.
  have hKU x (hx : K x) : U x by exists T=>//; exact: (hKT x hx).
  have hz x (hx : U x) (hn : ~K x) : q s x=0.
    by rewrite /q /u (euclidean_partition_bump_zero_off_ball ho hS hs hn) mul0r.
  move=>k; exact: (norm_class_higher_zero_extension (@scalar_absolute_value_norm R)
    hZ hKc hKU hz (norm_partition_smooth hq hs k)).
exists sigma, v; constructor.
- exact hsum.
- move=>x hx; exact: (finite_nonnegative_family_sum_plateau_bound
    hfin hsum hnonneg hx (hplateau x hx)).
- exact hsmooth.
- by move=>s hs x hx; exact: (norm_zero_extended_function_on (q s) hx).
- by move=>s hs x hx; exact: (norm_zero_extended_function_off (q s) hx).
- apply: (norm_partition_domain_agreement hN hZ _ hq).
  by move=>s hs x hx; symmetry; exact: (norm_zero_extended_function_on (q s) hx).
- exact hvsmooth.
- move=>s hs; exact: (real_function_support_in_closed_set
    (@metric_closed_ball_closed R _ s (10*federer_cover_radius Phi s)) (hzero s hs)).
- move=>s hs; exact: (real_function_compact_support_in_closed_set
    (@euclidean_closed_metric_ball_compact R m s (10*federer_cover_radius Phi s)) (@metric_closed_ball_closed R _ s (10*federer_cover_radius Phi s)) (hzero s hs)).
Qed.

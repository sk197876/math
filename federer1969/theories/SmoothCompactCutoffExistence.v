(** Federer (1969), 4.1.1, pp. 344–345: every compact
    subset of the original open finite normed source admits
    a smooth compact cutoff equal to one nearby. The original
    partition of 3.1.13 supplies the proved witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  LinearBasis SmoothCompactSet SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence
  SmoothCompactCutoffUP SmoothPartitionCutoffExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_cutoff_exists]: a smooth cutoff
    supported compactly in U and identically one near K exists,
    supporting the compact-support and restriction assertions in
    Federer 4.1.1, pp. 344–345. The finite basis expresses the
    original finite-dimensional source hypothesis. *)
Theorem smooth_compact_cutoff_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (K:smooth_compact_set hNX U):
  (forall x,U x ->norm_domain_interior NX U x) ->
  exists chi:X->R,is_smooth_compact_cutoff hNX U (smooth_compact_carrier K) chi.
Proof.
move=>hU.
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hNX U x).1 (hU x hx).
have hSingleton:forall A,([set U]:set (set (real_norm_metric_space hNX))) A ->open A.
  by move=>A ->.
have [J [I [v [hCount [hv hRef]]]]]:=
  @finite_norm_smooth_partition_exists R X NX hNX n b hb [set U] hSingleton.
rewrite bigcup_set1 in hv.
exact:(smooth_partition_compact_cutoff_exists hOpen hv
  (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
Qed.

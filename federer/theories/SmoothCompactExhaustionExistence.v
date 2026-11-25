(** Federer (1969), 4.1.1, p. 344: existence
    of auxiliary compact neighbourhood exhaustions for
    every original finite normed open source. The
    proved 3.1.13 partition supplies the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence
  CountableFiniteExhaustionSealed SmoothPartitionCompactExhaustion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_exhaustion_exists]: an
    increasing compact neighbourhood exhaustion exists,
    supporting the dual sequence assertion of Federer
    4.1.1, p. 344. Empty U and dimension
    zero are retained. *)
Theorem smooth_compact_exhaustion_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x):
  exists K:nat->smooth_compact_set hNX U,is_smooth_compact_exhaustion K.
Proof.
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx)).
have hPhi:forall A,([set U]:set (set (real_norm_metric_space hNX))) A ->open A.
  by move=>A ->.
have [J [I [v [hCount [hv hRef]]]]]:=@finite_norm_smooth_partition_exists R X NX hNX n b hb [set U] hPhi.
rewrite bigcup_set1 in hv.
pose C:=@CountableFiniteExhaustion.value J I hCount.
have hC:=@CountableFiniteExhaustion.laws J I hCount.
exists (@smooth_partition_exhaustion_compacts R X NX hNX U J I v hv C hC).
exact:(@smooth_partition_compact_exhaustion_laws R X NX hNX U hOpen J I v hv C hC).
Qed.

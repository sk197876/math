(** Federer (1969), 4.1.8, p. 361: the original
    Euclidean block join and split are continuous in
    the exact norm-metric presentations used by current domains.
    Reuse the existing inner-metric block maps and the
    proved norm/inner identity maps; no topology is replaced. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanDistributionMeasureContext
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section EuclideanBlockNormTopology.
Variable R:realType.
Variables m n:nat.
Local Notation N k := (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R k))).
Local Notation I k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [euclidean_block_join_norm_continuous]: the
    actual block join is continuous for the original
    factor and target norm topologies, supporting Federer
    4.1.8, p. 361, by the coordinate identification
    of 2.6.5, p. 120. *)
Theorem euclidean_block_join_norm_continuous:
  continuous (fun z:N m*N n=>(@euclidean_block_join R m n z:N (m+n))).
Proof.
pose f (z:N m*N n):(I m*I n)%type:=(z.1,z.2).
have hF:continuous f.
  apply:topological_pair_continuous.
  - move=>z;exact:(continuous_comp (@first_projection_continuous (N m) (N n) z)
      (@euclidean_distribution_norm_to_inner R m z.1)).
  - move=>z;exact:(continuous_comp (@second_projection_continuous (N m) (N n) z)
      (@euclidean_distribution_norm_to_inner R n z.2)).
move=>z.
exact:(continuous_comp (continuous_comp (@hF z)
  (@euclidean_block_join_continuous R m n (f z)))
  (@euclidean_distribution_inner_to_norm R (m+n) (euclidean_block_join (f z)))).
Qed.

(** Source for [euclidean_block_split_norm_continuous]: the
    actual block split is continuous for the same
    original norm topologies, supporting Federer 4.1.8,
    p. 361, including both empty coordinate blocks. *)
Theorem euclidean_block_split_norm_continuous:
  continuous (fun z:N (m+n)=>(@euclidean_block_split R m n z:(N m*N n)%type)).
Proof.
have hSplit:continuous (fun z:N (m+n)=>(@euclidean_block_split R m n z:(I m*I n)%type)).
  move=>z;exact:(continuous_comp (@euclidean_distribution_norm_to_inner R (m+n) z)
    (@euclidean_block_split_continuous R m n z)).
change (continuous (fun z:N (m+n)=>
  (((@euclidean_block_split R m n z).1:N m),((@euclidean_block_split R m n z).2:N n)))).
apply:topological_pair_continuous.
- move=>z;exact:(continuous_comp (continuous_comp (@hSplit z)
    (@first_projection_continuous (I m) (I n) (euclidean_block_split z)))
    (@euclidean_distribution_inner_to_norm R m (euclidean_block_split z).1)).
- move=>z;exact:(continuous_comp (continuous_comp (@hSplit z)
    (@second_projection_continuous (I m) (I n) (euclidean_block_split z)))
    (@euclidean_distribution_inner_to_norm R n (euclidean_block_split z).2)).
Qed.
End EuclideanBlockNormTopology.

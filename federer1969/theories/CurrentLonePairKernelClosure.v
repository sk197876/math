(** Federer (1969), 4.1.18, p. 377:
    the full original kernel identity on
    arbitrary open U. Its two inclusions
    are the proved ordinary-convolution graph
    approximation and the earlier actual q-kernel
    closedness in the original J topology. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairCost
  CurrentCompactSmoothDivergenceUP CurrentCompactSmoothDivergenceKernel
  CurrentLonePairKernelClosed CurrentLonePairKernelGraphDensity
  CurrentLonePairTopology OpenFamilyTopologyMathcomp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section KernelClosure.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation q := (@CurrentLonePair.map R h2 n m U hU).
Local Notation graph :=
  (@is_current_compact_smooth_divergence_pair R h2 n m U hU).
Local Notation hTopology := (@current_lone_pair_topology_laws R h2 n m U hU).

(** Source for [current_lone_pair_kernel_graph_iff]:
    the original kernel is precisely the
    set of pairs admitting every positive
    J-error approximation by the original smooth
    divergence graph, Federer 4.1.18, p. 377.
    The original open domain and both
    actual coefficient fields remain unchanged. *)
Theorem current_lone_pair_kernel_graph_iff (v : P) :
  q v=0 <-> forall epsilon : R, 0 < epsilon ->
    exists w : P, graph w /\ J (v-w)%R < epsilon.
Proof.
split; first exact: (@current_lone_pair_kernel_graph_dense R h2 n m U hU v).
move=> hApprox.
apply: (@current_lone_pair_kernel_closed R h2 n m U hU v)=> epsilon hEpsilon.
have [w [hW hDistance]] := hApprox epsilon hEpsilon.
exists w; split; last exact: hDistance.
exact: (@current_compact_smooth_divergence_pair_kernel R h2 n m U hU w hW).
Qed.

(** Source for [current_lone_pair_kernel_graph_closure]:
    the literal displayed equality ker q=
    Closure{(div eta,eta):eta compact smooth on U}
    in Federer 4.1.18, p. 377,
    with Closure taken in the actual original
    J-seminorm topology on the full raw pair space. *)
Theorem current_lone_pair_kernel_graph_closure :
  [set v : P | q v=0]=
    @closure (open_family_topological_space hTopology.1) graph.
Proof.
apply: funext=> v; apply: propext.
exact: (iff_trans (current_lone_pair_kernel_graph_iff v)
  (iff_sym (@current_lone_pair_closure_balls R h2 n m U hU graph v))).
Qed.
End KernelClosure.

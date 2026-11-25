(** Federer (1969), 3.3.3, p. 288: the near-fibre
    incidence sets are Suslin. Keep the original A and
    actual projection, and derive the metric and projection
    constraints from their proved continuous maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm InnerNormedTopology
  EuclideanProjectionSpace EuclideanProjectionMetric TopologicalProductMaps
  MetricProductBackground TopologicalBorel BorelFamilyBasic BorelClosedProjection
  SuslinSetUP SuslinPreimages BorelSuslinImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports
  numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_near_fibre_incidence]: the sets
    S_i in the proof of Federer 3.3.3, p. 288,
    with natural index i shifted by one. The projection
    equality is written as p(x-a)=0 by linearity. *)
Definition structure_near_fibre_incidence (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) i:
    set (inner_metric_space (@euclidean_inner_productP R n)*
      (inner_metric_space (@euclidean_inner_productP R n)*euclidean_projection_space R n m)):=
  [set z|A z.1 /\
    0<inner_norm (@euclidean_inner_productP R n) (z.1-z.2.1)<((i.+1)%:R:R)^-1 /\
    euclidean_projection_linear z.2.2 (z.1-z.2.1)=0].

(** Source for [structure_near_fibre_incidence_suslin]: the
    first assertion of the proof of Federer 3.3.3,
    p. 288. Original-source membership is a continuous
    Suslin preimage; the near-point band is open and
    the actual linear kernel equation is closed. *)
Theorem structure_near_fibre_incidence_suslin (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) i:
  is_suslin_set R A ->is_suslin_set R (structure_near_fibre_incidence (m:=m) A i).
Proof.
move=>hA.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=orthogonal_projection_metric_space R n m.
pose Q:=[the metricType R of metric_product E P].
pose T:=[the metricType R of metric_product E Q].
pose D (z:T):E:=z.1-z.2.1.
have hD:continuous D.
  move=>z; apply:cvgB; first exact:(@first_projection_continuous E Q z).
  exact:(continuous_comp (@second_projection_continuous E Q z)
    (@first_projection_continuous E P z.2)).
pose N (z:T):R^o:=inner_norm (@euclidean_inner_productP R n) (D z).
have hN:continuous N by move=>z; exact:(cvg_norm (hD z)).
pose F (z:T):Y:=euclidean_projection_linear z.2.2 (D z).
have hPair:continuous (fun z:T=>(z.2.2,D z)).
  apply:topological_pair_continuous; last exact:hD.
  move=>z; exact:(continuous_comp (@second_projection_continuous E Q z)
    (@second_projection_continuous E P z.2)).
have hF:continuous F.
  move=>z; exact:(continuous_comp (hPair z)
    (@euclidean_projection_evaluation_continuous R n m (z.2.2,D z))).
have hNear:open [set z:T|0<N z<((i.+1)%:R:R)^-1].
  have he:[set z:T|0<N z<((i.+1)%:R:R)^-1]=
    (N @^-1` [set t:R^o|0<t]) `&`
    (N @^-1` [set t:R^o|t<((i.+1)%:R:R)^-1]).
    apply/seteqP; split=>z; [by move=>/andP|by move=>/andP].
  rewrite he; apply:openI.
  - exact:((continuousP N).1 hN _ (@open_gt R 0)).
  - exact:((continuousP N).1 hN _ (@open_lt R ((i.+1)%:R:R)^-1)).
have hZeroY:closed [set (0:Y)].
  apply:accessible_closed_set1; apply:hausdorff_accessible; exact:(@metric_hausdorff R Y).
have hZero:closed [set z:T|F z=0].
  exact:((continuous_closedP F).1 hF [set (0:Y)] hZeroY).
have hB:borel_set ([set z:T|0<N z<((i.+1)%:R:R)^-1] `&` [set z:T|F z=0]).
  exact:(borel_family_binary_intersection (borel_sets_family T)
    (open_borel_set hNear) (closed_borel_set hZero)).
change (is_suslin_set R ((@fst E Q @^-1` A) `&`
  ([set z:T|0<N z<((i.+1)%:R:R)^-1] `&` [set z:T|F z=0]))).
apply:suslin_binary_intersection.
- exact:(continuous_preimage_suslin (@first_projection_continuous E Q) hA).
- exact:metric_borel_suslin hB.
Qed.

(** Federer (1969), 3.3.2, pp. 287–288: the original cone has
    open incidence, so a compact subset remains in nearby cones.
    This fixed-radius fixed-aperture section of the joint argument
    is sufficient before taking the open union over r and s. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm InnerNormedTopology EuclideanProjectionSpace
  RealMetricBackground TopologicalProductMaps CompactProductTube
  StructureCone StructureProjectionKernel StructureProjectionCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports
  numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_incidence_open]: supporting the
    first open set in the proof of Federer 3.3.2, p. 287.
    At every fixed finite radius and aperture, the incidence
    of (a,p,x) in the original X(a,r,ker p,s) is open. No
    projected-distance or continuity assumption is supplied. *)
Theorem structure_cone_incidence_open (R:realType) n m
    (hmn:(m<=n)%N) (r s:R):
  @open ((inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m)*
    inner_metric_space (@euclidean_inner_productP R n))%type
    [set z|structure_cone (structure_projection_kernel hmn z.1.2)
      z.1.1 r%:E s z.2].
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=(E*euclidean_projection_space R n m)%type.
pose D (z:P*E):E:=z.2-z.1.1.
have hD:continuous D.
  move=>z; apply:cvgB; first exact:(@second_projection_continuous P E z).
  exact:(continuous_comp (@first_projection_continuous P E z)
    (@first_projection_continuous E (euclidean_projection_space R n m) z.1)).
have hPair:continuous (fun z:P*E=>(z.1.2,D z)).
  apply:topological_pair_continuous; last exact:hD.
  move=>z; exact:(continuous_comp (@first_projection_continuous P E z)
    (@second_projection_continuous E (euclidean_projection_space R n m) z.1)).
have hImage:continuous (fun z:P*E=>(euclidean_projection_linear z.1.2 (D z):Y)).
  move=>z; exact:(continuous_comp (hPair z)
    (@euclidean_projection_evaluation_continuous R n m (z.1.2,D z))).
pose F (z:P*E):R^o:=inner_norm (@euclidean_inner_productP R n) (D z)-
  s^-1*inner_norm (@euclidean_inner_productP R m)
    (euclidean_projection_linear z.1.2 (D z)).
have hF:continuous F.
  move=>z; apply:cvgB.
  - exact:(cvg_norm (hD z)).
  - apply:cvgM; first exact:cvg_cst.
    exact:(cvg_norm (hImage z)).
pose H (z:P*E):R^o:=r-inner_norm (@euclidean_inner_productP R n) (D z).
have hH:continuous H.
  move=>z; apply:cvgB; first exact:cvg_cst.
  exact:(cvg_norm (hD z)).
have he:[set z:P*E|structure_cone (structure_projection_kernel hmn z.1.2)
    z.1.1 r%:E s z.2]=
    (F @^-1` [set t:R^o|0<t]) `&` (H @^-1` [set t:R^o|0<t]).
  apply/seteqP; split=>z.
  - move/(structure_projection_coneE hmn z.1.2 z.1.1 r%:E s z.2)=>[hAngle hRadius].
    split.
    + change (is_true (0<F z)); by rewrite /F /D subr_gt0.
    + change (is_true (0<H z)); rewrite /H /D subr_gt0.
      by move:hRadius; rewrite lte_fin.
  - move=>[hAngle hRadius]; apply/(structure_projection_coneE hmn z.1.2 z.1.1 r%:E s z.2).
    split.
    + by move:hAngle; rewrite /F /D /= subr_gt0.
    + rewrite lte_fin; by move:hRadius; rewrite /H /D /= subr_gt0.
rewrite he; apply:openI.
- exact:((continuousP F).1 hF [set t:R^o|0<t] (@open_gt R 0)).
- exact:((continuousP H).1 hH [set t:R^o|0<t] (@open_gt R 0)).
Qed.

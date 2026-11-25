(** Federer (1969), 3.3.2, p. 287: joint openness in
    the centre, radius, projection and aperture. The parameter
    product is grouped as ((a,p),(r,s)); this merely permutes
    the printed product factors. Positive aperture turns the
    inverse inequality into an equivalent polynomial inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  InnerNormedTopology EuclideanProjectionSpace TopologicalProductMaps
  CompactProductTube StructureCone StructureProjectionKernel StructureProjectionCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports
  numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_positive_joint_cone_open]: supporting
    the first displayed open containment set in the proof of
    Federer 3.3.2, p. 287. The original cone incidence
    is jointly open throughout the positive-aperture domain. *)
Theorem structure_positive_joint_cone_open (R:realType) n m (hmn:(m<=n)%N):
  @open (((inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m)*(R^o*R^o))*
    inner_metric_space (@euclidean_inner_productP R n))%type
    [set z|0<z.1.2.2 /\
      structure_cone (structure_projection_kernel hmn z.1.1.2)
        z.1.1.1 (z.1.2.1)%:E z.1.2.2 z.2].
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=(E*euclidean_projection_space R n m)%type.
pose Q:=(P*(R^o*R^o))%type.
pose D (z:Q*E):E:=z.2-z.1.1.1.
have hAP:continuous (fun z:Q*E=>z.1.1).
  move=>z; exact:(continuous_comp (@first_projection_continuous Q E z)
    (@first_projection_continuous P (R^o*R^o)%type z.1)).
have hRS:continuous (fun z:Q*E=>z.1.2).
  move=>z; exact:(continuous_comp (@first_projection_continuous Q E z)
    (@second_projection_continuous P (R^o*R^o)%type z.1)).
have hR:continuous (fun z:Q*E=>(z.1.2.1:R^o)).
  move=>z; exact:(continuous_comp (hRS z) (@first_projection_continuous R^o R^o z.1.2)).
have hS:continuous (fun z:Q*E=>(z.1.2.2:R^o)).
  move=>z; exact:(continuous_comp (hRS z) (@second_projection_continuous R^o R^o z.1.2)).
have hD:continuous D.
  move=>z; apply:cvgB; first exact:(@second_projection_continuous Q E z).
  exact:(continuous_comp (hAP z) (@first_projection_continuous E (euclidean_projection_space R n m) z.1.1)).
have hPair:continuous (fun z:Q*E=>(z.1.1.2,D z)).
  apply:topological_pair_continuous; last exact:hD.
  move=>z; exact:(continuous_comp (hAP z) (@second_projection_continuous E (euclidean_projection_space R n m) z.1.1)).
have hImage:continuous (fun z:Q*E=>(euclidean_projection_linear z.1.1.2 (D z):Y)).
  move=>z; exact:(continuous_comp (hPair z)
    (@euclidean_projection_evaluation_continuous R n m (z.1.1.2,D z))).
pose F (z:Q*E):R^o:=z.1.2.2*inner_norm (@euclidean_inner_productP R n) (D z)-
  inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear z.1.1.2 (D z)).
have hF:continuous F.
  move=>z; apply:cvgB; last exact:(cvg_norm (hImage z)).
  exact:(cvgM (hS z) (cvg_norm (hD z))).
pose H (z:Q*E):R^o:=z.1.2.1-inner_norm (@euclidean_inner_productP R n) (D z).
have hH:continuous H.
  move=>z; exact:(cvgB (hR z) (cvg_norm (hD z))).
pose S (z:Q*E):R^o:=z.1.2.2.
have he:[set z:Q*E|0<z.1.2.2 /\
    structure_cone (structure_projection_kernel hmn z.1.1.2)
      z.1.1.1 (z.1.2.1)%:E z.1.2.2 z.2]=
    (S @^-1` [set t:R^o|0<t]) `&`
    ((F @^-1` [set t:R^o|0<t]) `&` (H @^-1` [set t:R^o|0<t])).
  apply/seteqP; split=>z.
  - move=>[hs hCone]; have [ha hr]:=(structure_projection_coneE hmn z.1.1.2 z.1.1.1
      (z.1.2.1)%:E z.1.2.2 z.2).1 hCone.
    split=>//; split.
    + change (is_true (0<F z)); rewrite /F /D subr_gt0.
      by move:ha; rewrite mulrC ltr_pdivrMr // mulrC.
    + change (is_true (0<H z)); rewrite /H /D subr_gt0.
      by move:hr; rewrite lte_fin.
  - move=>[hs [ha hr]]; split=>//.
    apply/(structure_projection_coneE hmn z.1.1.2 z.1.1.1
      (z.1.2.1)%:E z.1.2.2 z.2); split.
    + rewrite mulrC ltr_pdivrMr // mulrC.
      by move:ha; rewrite /F /D /= subr_gt0.
    + rewrite lte_fin; by move:hr; rewrite /H /D /= subr_gt0.
rewrite he; apply:openI.
- exact:((continuousP S).1 hS [set t:R^o|0<t] (@open_gt R 0)).
- apply:openI.
  + exact:((continuousP F).1 hF [set t:R^o|0<t] (@open_gt R 0)).
  + exact:((continuousP H).1 hH [set t:R^o|0<t] (@open_gt R 0)).
Qed.

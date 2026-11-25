(** Federer (1969), 4.1.5, p. 350:
    a bounded product of evaluation functionals
    gives weak compactness in the actual
    continuous dual once the original bounds
    imply continuity. The abstract dual carrier
    is used only through its public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormOpenTopology OpenFamilyTopologyUP
  OpenFamilyTopologyMathcomp ContinuousRealDual ContinuousRealDualSubspace LinearSubspaceRepresentationUP
  WeakEvaluationTopologyUP IsotropyGroupTopology SubtypeCompactHausdorff
  CompactScalarVectorIdentification BoundedLinearProductCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_continuous_real_dual_weak_compact]: the
    product-to-actual-dual step in the final
    compactness assertion of Federer 4.1.5,
    p. 350. The continuity premise must
    be proved from the original bounds for
    the actual test space. *)
Theorem bounded_continuous_real_dual_weak_compact (R:realType) (E:lmodType R)
    (SO:set (set E)) (hSO:is_open_family_topology SO) (B:E->R):
  (forall L:Hom E R^o,(forall x,L x<=B x) ->
    open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) L) ->
  @compact (open_family_topological_space
    (@continuous_real_dual_weak_laws R E SO hSO).1)
    [set T|forall x,(@continuous_real_dual_evaluation R E SO hSO T) x<=B x].
Proof.
move=>hAdmissible.
pose DD:=@continuous_real_dual_space R E SO hSO.
pose ed:=@continuous_real_dual_evaluation R E SO hSO.
pose OW:=@continuous_real_dual_weak_opens R E SO hSO.
pose hWeak:=@continuous_real_dual_weak_laws R E SO hSO.
pose W:=open_family_topological_space hWeak.1.
pose P:=prod_topology (fun _:E=>R).
pose Q:set P:=@bounded_linear_product_set R E B.
pose QT:=set_type Q.
pose L:=fun a:QT=>@HomMap R E R^o (fun x=>val a x)
  (introT (asboolP _) (set_valP a).1).
have hExists a:exists t:DD,ed t=L a.
  apply:(@continuous_real_dual_represents R E SO hSO (L a)).
  apply:hAdmissible=>x; exact:(set_valP a).2 x.
have[q hEvaluation]:=choice hExists.
have hCoordinate x:continuous (fun a:QT=>(ed (q a) x:real_norm_metric_space (@scalar_absolute_value_norm R))).
  have hProduct:continuous (val:QT->P).
    exact:initial_continuous.
  have hProjection:continuous (fun a:P=>(a x:R)):=@proj_continuous E (fun _:E=>R) x.
  have hNative:continuous (fun a:QT=>(val a x:real_line_metric R)).
    move=>a; exact:(continuous_comp (hProduct a) (hProjection (val a))).
  have hScalar:continuous (fun a:QT=>(val a x:real_norm_metric_space (@scalar_absolute_value_norm R))).
    move=>a; exact:(continuous_comp (hNative a) (@real_scalar_norm_identity_continuous R (val a x))).
  have hEq:(fun a:QT=>ed (q a) x)=(fun a:QT=>val a x).
    apply:funext=>a; by rewrite (hEvaluation a).
  by rewrite hEq.
have hSource:is_open_family_topology (@open QT).
  constructor.
  - exact:openT.
  - exact:openI.
  - move=>I A hA; apply:bigcup_open=>i _; exact:hA.
have hMap:continuous (fun a:QT=>(q a:W)).
  apply/continuousP.
  apply:(hWeak.2 QT (@open QT) hSource q).2=>x.
  by move/continuousP:(hCoordinate x).
have hQCompact:compact Q:=@bounded_linear_product_compact R E B.
have hCompact:compact ((fun a:QT=>(q a:W)) @` setT).
  apply:continuous_compact (set_type_compact_whole hQCompact).
  exact:continuous_subspaceT hMap.
have hImage:((fun a:QT=>(q a:W)) @` setT)=
    [set t:W|forall x,ed t x<=B x].
  apply/seteqP; split.
  - move=>t [a _ <-] x; rewrite (hEvaluation a); exact:(set_valP a).2 x.
  - move=>t hBound.
    have hMember:Q (fun x=>ed t x).
      split; first exact:hom_linear; exact hBound.
    pose a:QT:=exist _ (fun x=>ed t x) (mem_set hMember).
    exists a; first exact I.
    apply:(subspace_representation_injective (@continuous_real_dual_model_laws R E SO hSO)).
    rewrite (hEvaluation a); apply:hom_ext=>x; reflexivity.
rewrite hImage in hCompact; exact hCompact.
Qed.

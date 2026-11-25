(** Federer (1969), 4.1.1, pp. 344–345; Menne (2016),
    Remarks 2.14–2.17, p. 996: the literal final topology and
    the locally convex inductive topology have the same continuous
    linear maps to seminorm-defined locally convex spaces. The
    proof does not identify the two topologies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP RealSeminormOperations OpenFamilyTopologyUP
  FinalOpenTopologyUP DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  InductiveLimitSeminormFamilyUP InductiveLimitSeminormFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InductiveMapping.
Variable R:realType.
Variable E:lmodType R.
Variable J:Type.
Variable W:J->lmodType R.
Variable I:J->Type.
Variable p:forall j,I j->W j->R.
Variable inc:forall j,Hom (W j) E.
Variable O:forall j,set (set (W j)).
Hypothesis hp:forall j,is_directed_seminorm_family (@p j).
Hypothesis hO:forall j,is_seminorm_family_topology (@p j) (@O j).
Variable T:set (set E).
Hypothesis hT:is_inductive_limit_open_topology p inc T.
Local Notation C := (@compatible_seminorm_index R E J W I p inc).
Local Notation q := (fun c:C=>compatible_seminorm_value c).
Local Notation hq := (inductive_compatible_seminorms_directed inc hp).

(** Source for [inductive_limit_step_continuous]: each original
    fixed-support step includes continuously into the locally
    convex inductive limit, Menne (2016), Definition 2.13, p. 996. *)
Theorem inductive_limit_step_continuous j :
  open_family_continuous (@O j) T (@inc j).
Proof.
apply:(@seminorm_family_bounded_linear_continuous R (W j) E (I j) C
  (@p j) q (@O j) T (hp j) (hO j) hT (@inc j))=>c.
exact:(compatible_seminorm_laws c).2 j.
Qed.

(** Source for [inductive_limit_linear_mapping]: linear continuity
    out of the locally convex inductive limit is equivalent to
    continuity on all its steps, Menne (2016), Remark 2.17,
    p. 996. This retains arbitrary seminorm-generated targets. *)
Theorem inductive_limit_linear_mapping (F:lmodType R) (A:Type)
    (r:A->F->R) (Q:set (set F))
    (hr:is_directed_seminorm_family r) (hQ:is_seminorm_family_topology r Q)
    (L:Hom E F) :
  open_family_continuous T Q L <->
  forall j,open_family_continuous (@O j) Q (fun w=>L (@inc j w)).
Proof.
split.
- move=>hL j; exact:open_family_continuous_compose (inductive_limit_step_continuous j) hL.
- move=>hSteps.
  apply:(@seminorm_family_bounded_linear_continuous R E F C A q r T Q hq hT hQ L)=>a.
  have hCompat:is_step_compatible_seminorm p inc (fun x=>r a (L x)).
    split.
    + exact:(real_seminorm_linear_precompose (directed_seminorm_laws hr a) (hom_linear L)).
    + move=>j.
      have hj:=hSteps j.
      have hLinear:linear (fun w=>L (@inc j w)) by move=>c x y; rewrite !linearP.
      pose Lj:Hom (W j) F:=@HomMap R (W j) F (fun w=>L (@inc j w))
        (introT (asboolP _) hLinear).
      exact:(@seminorm_family_continuous_linear_bound R (W j) F (I j) A
        (@p j) r (@O j) Q (hp j) hr (hO j) hQ Lj hj a).
  exists (@CompatibleSeminorm R E J W I p inc (fun x=>r a (L x)) hCompat),1.
  split; first exact:ler01.
  by move=>x; rewrite /= mul1r.
Qed.

(** Source for [final_topology_finer_than_inductive]: every
    locally convex inductive-open set is final-open, Menne (2016),
    Remark 2.17, p. 996, comparing with the literal topology of
    Federer 4.1.1, p. 344. Equality is not asserted. *)
Theorem final_topology_finer_than_inductive (S:set (set E)) :
  is_final_open_topology O (fun j w=>@inc j w) S ->
  forall A,T A -> S A.
Proof.
move=>hS A hA; apply:(hS.2 A).2=>j.
exact:inductive_limit_step_continuous j A hA.
Qed.

(** Source for [final_inductive_linear_continuity_iff]: the two
    topologies have the same continuous linear maps into a
    seminorm-defined locally convex space, Menne (2016), Remark
    2.17, p. 996. For real scalars this identifies the distribution
    dual while preserving Federer's topology, 4.1.1, p. 345. *)
Theorem final_inductive_linear_continuity_iff (S:set (set E))
    (F:lmodType R) (A:Type) (r:A->F->R) (Q:set (set F))
    (hr:is_directed_seminorm_family r) (hQ:is_seminorm_family_topology r Q)
    (L:Hom E F) :
  is_final_open_topology O (fun j w=>@inc j w) S ->
  (open_family_continuous S Q L <-> open_family_continuous T Q L).
Proof.
move=>hS.
rewrite (@final_open_topology_mapping J (fun j=>W j) E F O
  (fun j w=>@inc j w) S Q L hS).
exact:iff_sym (inductive_limit_linear_mapping hr hQ L).
Qed.
End InductiveMapping.

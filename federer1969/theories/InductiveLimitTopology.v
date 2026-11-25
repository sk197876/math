(** Federer (1969), 4.1.1, pp. 344–345; Menne (2016),
    Definition 2.13 and Remark 2.17, p. 996: existence of the
    locally convex comparison topology. The generic opaque
    seminorm-topology constructor is reused. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP DirectedSeminormFamilyUP
  DirectedSeminormTopologySealed InductiveLimitSeminormFamilyUP InductiveLimitSeminormFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InductiveTopologyExistence.
Variable R:realType.
Variable E:lmodType R.
Variable J:Type.
Variable W:J->lmodType R.
Variable I:J->Type.
Variable p:forall j,I j->W j->R.
Variable inc:forall j,Hom (W j) E.
Hypothesis hp:forall j,is_directed_seminorm_family (@p j).

(** Source for [inductive_limit_opens]: the independently
    specified compatible-seminorm topology of Menne (2016),
    Definition 2.13, p. 996, used to qualify the topology in
    Federer 4.1.1, p. 344. Its witness remains opaque. *)
Definition inductive_limit_opens:set (set E) :=
  @DirectedSeminormTopology.opens R E
    (@compatible_seminorm_index R E J W I p inc)
    (fun q=>compatible_seminorm_value q)
    (inductive_compatible_seminorms_directed inc hp).

(** Source for [inductive_limit_opens_laws]: the constructed
    topology has exactly the independent compatible-seminorm
    neighbourhoods, Menne (2016), Definition 2.13, p. 996. *)
Theorem inductive_limit_opens_laws :
  is_inductive_limit_open_topology p inc inductive_limit_opens.
Proof. exact:DirectedSeminormTopology.laws. Qed.
End InductiveTopologyExistence.

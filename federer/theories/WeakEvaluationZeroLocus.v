(** Federer (1969), 4.1.1, pp. 344–345: simultaneous
    vanishing of specified real evaluations defines a
    weakly closed set. This supporting topology fact is
    applied to the compact-support annihilation criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenTopology OpenFamilyTopologyUP
  WeakEvaluationTopologyUP WeakEvaluationTopologyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weak_evaluation_zero_locus_closed]: an
    intersection of zero sets of weakly continuous real
    evaluations is closed, supporting E'_K in Federer
    4.1.1, p. 344. Arbitrary test families are allowed. *)
Theorem weak_evaluation_zero_locus_closed (R:realType) (E D:choiceType)
    (ev:D->E->R) (O:set (set D)) (hO:is_weak_evaluation_topology ev O)
    (I:set E):
  O (~` [set d:D|forall e,I e ->ev d e=0]).
Proof.
pose S:=real_norm_metric_space (@scalar_absolute_value_norm R).
have hNonzero:norm_open_family (@scalar_absolute_value_norm R) [set t:R^o|t<>0].
  exact:(@closed_openC S [set (0:R^o)]
    (compact_closed (@metric_hausdorff R S) (@compact_set1 S 0))).
pose A:={e:E|I e}.
have hUnion:O (\bigcup_(e:A) [set d:D|ev d (proj1_sig e)<>0]).
  apply:(@open_family_union D O hO.1 A)=>e.
  exact:(weak_evaluation_continuous hO (proj1_sig e) hNonzero).
have hEq:(~` [set d:D|forall e,I e ->ev d e=0])=
    (\bigcup_(e:A) [set d:D|ev d (proj1_sig e)<>0]).
  apply:funext=>d; apply:propext; split.
  - move=>hNot.
    have hSome:exists e,I e /\ ev d e<>0.
      case:(pselect (exists e,I e /\ ev d e<>0))=>// hNone.
      apply:False_ind; apply:hNot=>e he.
      case:(pselect (ev d e=0))=>// hn.
      exact:False_ind _ (hNone (ex_intro _ e (conj he hn))).
    have [e [he hn]]:=hSome; exists (exist _ e he); first exact Logic.I.
    exact hn.
  - move=>[e _ hn] hZero; exact:hn (hZero (proj1_sig e) (proj2_sig e)).
by rewrite hEq.
Qed.

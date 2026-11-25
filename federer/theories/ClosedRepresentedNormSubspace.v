(** Federer (1969), 4.1.12, p. 368: a closed
    subspace of the complete finite-flat current space
    is complete. This supporting adapter retains an
    arbitrary opaque carrier and reuses the earlier
    closed-subset and isometric-transfer theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP RealSeminormOperations
  NormMetric LinearSubspaceRepresentationUP CompleteMetricUP MetricSubsetBackground
  MetricClosedSubsetCompleteness CompleteMetricIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ClosedRepresentedNormSubspace.
Variable R:realType.
Variables V W:lmodType R.
Variable N:V->R.
Hypothesis hN:is_real_norm N.
Variable S:subspace V.
Variable inc:Hom W V.
Hypothesis hW:is_linear_subspace_representation S inc.

(** Source for [represented_subspace_norm]: the given
    ambient norm restricted through the original linear
    inclusion, supporting Federer 4.1.12, p. 368.
    No carrier or norm construction is exposed. *)
Definition represented_subspace_norm (w:W):R:=N (inc w).

(** Source for [represented_subspace_norm_laws]: the
    inherited original norm is definite on the opaque
    subspace carrier, supporting Federer 4.1.12,
    p. 368. Only the injective inclusion is used. *)
Theorem represented_subspace_norm_laws:is_real_norm represented_subspace_norm.
Proof.
exact:(@real_norm_injective_precompose R W V N hN inc
  (subspace_representation_injective hW)).
Qed.

(** Source for [closed_represented_norm_subspace_complete]:
    an original closed subspace of a complete normed
    space is complete with its inherited norm,
    supporting the flat-chain completeness assertion in
    Federer 4.1.12, p. 368. The supplied carrier
    is used solely through its independent image laws. *)
Theorem closed_represented_norm_subspace_complete:
  is_complete_metric_space (real_norm_metric_space hN)->
  closed (fun v:real_norm_metric_space hN=>S v)->
  is_complete_metric_space (real_norm_metric_space represented_subspace_norm_laws).
Proof.
move=>hComplete hClosed.
pose T:=real_norm_metric_space hN.
pose E:=real_norm_metric_space represented_subspace_norm_laws.
pose A:set T:=fun v=>S v.
pose Y:=[the metricType R of metric_subset A].
pose f (w:E):Y:=@exist T (fun v=>v \in A) (inc w)
  (mem_set (subspace_representation_member hW w)).
have hInjective:injective f.
  move=>x y hEqual;apply:(subspace_representation_injective hW).
  exact:(congr1 (@set_val T A) hEqual).
have hSurjective:forall y:Y,exists x:E,f x=y.
  move=>y.
  have [x hX]:=subspace_representation_full hW (set_valP y).
  exists x;apply:val_inj;exact:hX.
have [g hRight]:=choice hSurjective.
have hLeft:cancel f g.
  move=>x;apply:hInjective;exact:hRight (f x).
have hDistance:forall x y:E,mdist (f x) (f y)=mdist x y.
  move=>x y;change (N (inc x-inc y)=N (inc (x-y))).
  by rewrite linearB.
apply:(@complete_metric_isometric_bijection R E Y f g hLeft hRight hDistance).
exact:(@complete_closed_metric_subset R T A hComplete hClosed).
Qed.
End ClosedRepresentedNormSubspace.

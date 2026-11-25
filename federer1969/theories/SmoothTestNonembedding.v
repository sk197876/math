(** Federer (1969), 4.1.1, p. 344: corrected
    nonembedding of D(U,Y) in E(U,Y). The assertion
    holds for noncompact U and nonzero Y, hence
    for nonempty open U in a nonzero real
    finite-dimensional source. Compact domains give
    the omitted zero-dimensional exception. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP InitialOpenTopologyUP LinearSubspaceRepresentationUP
  FinalTopologyEscapingSequence NormCompactOpenDomain SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothTestEscapingSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestNonembedding.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_test_noncompact_nonembedding]: the
    inclusion is not a homeomorphic embedding for
    noncompact U and nonzero Y, correcting the
    exception in Federer 4.1.1, p. 344. *)
Theorem smooth_test_noncompact_nonembedding:
  ~compact [set x:real_norm_metric_space hNX|U x] ->
  (exists y:Y,y<>0) ->
  ~is_initial_open_topology (smooth_function_opens hD) (smooth_test_inclusion hE)
    (smooth_test_opens hE hD).
Proof.
move=>hNoncompact hNonzero.
have [s [hNe [hCvg hEscape]]]:=@smooth_test_escaping_sequence_exists R X Y NX NY hNX hNY
  d b hb U hU E ev hE D hD hNoncompact hNonzero.
exact (@final_topology_escaping_sequence_nonembedding
  _ (smooth_fixed_test_space hE) (smooth_test_space hE) E
  (smooth_function_opens hD) (smooth_test_opens hE hD) (smooth_test_step_opens hE hD)
  (smooth_test_inclusion hE) (fun K f=>smooth_test_step hE K f)
  (fun K f=>smooth_fixed_test_inclusion hE K f) s 0
  (smooth_function_topology_laws hD).1 (smooth_function_topology_hausdorff hE hD)
  (subspace_representation_injective (smooth_test_space_laws hE))
  (fun K f=>@smooth_test_step_evaluation R X Y NX NY hNX hNY U E ev hE K f) (smooth_test_final_topology_laws hE hD)
  (fun K=>@smooth_test_step_relative_topology R X Y NX NY hNX hNY U E ev hE D hD K) hNe hCvg hEscape).
Qed.

(** Source for [smooth_test_nonzero_source_nonembedding]:
    the printed assertion holds on every nonempty
    open domain in a nonzero finite-dimensional
    real source, with nonzero target. This adds
    the necessary source qualification to Federer
    4.1.1, p. 344. *)
Theorem smooth_test_nonzero_source_nonembedding:
  (exists x:X,x<>0) ->U !=set0 ->(exists y:Y,y<>0) ->
  ~is_initial_open_topology (smooth_function_opens hD) (smooth_test_inclusion hE)
    (smooth_test_opens hE hD).
Proof.
move=>hX hU0 hY; apply:smooth_test_noncompact_nonembedding=>//.
apply:(@real_norm_nonempty_open_noncompact R X NX hNX U hX _ hU0).
rewrite openE=>x hx.
exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
Qed.
End TestNonembedding.

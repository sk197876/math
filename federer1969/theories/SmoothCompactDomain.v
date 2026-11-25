(** Federer (1969), 4.1.1, p. 344: the printed exception
    to nonembedding misses compact open domains, in particular
    a nonempty zero-dimensional source. This supporting theorem
    proves that on a compact domain the inclusion D into E is
    an actual homeomorphism, with its original topologies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP ModuleQuotient RealNormUP ContinuousMultilinearSealed OpenFamilyTopologyUP
  InitialOpenTopologyUP FinalOpenTopologyUP LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSubspaces
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section CompactDomain.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable K:smooth_compact_set hNX U.
Hypothesis hCover:forall x,U x -> smooth_compact_carrier K x.
Local Notation DK := (smooth_fixed_test_space hE K).
Local Notation DT := (smooth_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE K).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation j := (smooth_test_step hE K).
Local Notation EO := (smooth_function_opens hD).
Local Notation PK := (smooth_test_step_opens hE hD K).
Local Notation SO := (smooth_test_opens hE hD).

(** Source for [smooth_compact_domain_fixed_member]: every
    smooth function has its support in the compact domain,
    supporting the zero-dimensional correction to Federer
    4.1.1, p. 344. *)
Lemma smooth_compact_domain_fixed_member f:
  smooth_fixed_support_subspace hE K (hom_of_linear (linear_id E) f).
Proof. move=>x hx; exact:hCover x hx.1. Qed.

(** Source for [smooth_compact_domain_fixed_map]: the original
    function regarded as a fixed-support test function on a
    compact domain, supporting the correction to Federer 4.1.1,
    p. 344. The lift is opaque and proved before use. *)
Definition smooth_compact_domain_fixed_map:Hom E DK:=
  @LinearSubspaceLift.map R E DK E (smooth_fixed_support_subspace hE K) k
    (smooth_fixed_test_space_laws hE K) (hom_of_linear (linear_id E))
    smooth_compact_domain_fixed_member.

(** Source for [smooth_compact_domain_fixed_evaluation]: the
    lift preserves the actual smooth function, supporting the
    compact-domain correction to Federer 4.1.1, p. 344. *)
Lemma smooth_compact_domain_fixed_evaluation f:
  k (smooth_compact_domain_fixed_map f)=f.
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [smooth_compact_domain_fixed_continuous]: every
    smooth function becomes a test function continuously when
    the domain is compact, supporting the correction to Federer
    4.1.1, p. 344. *)
Lemma smooth_compact_domain_fixed_continuous:
  open_family_continuous EO PK smooth_compact_domain_fixed_map.
Proof.
apply:(initial_open_topology_mapping EO smooth_compact_domain_fixed_map
  (@smooth_test_step_relative_topology R X Y NX NY hNX hNY U E ev hE D hD K)).2.
have he:(fun f:E=>k (smooth_compact_domain_fixed_map f))=id.
  apply:funext=>f; exact:smooth_compact_domain_fixed_evaluation.
rewrite he; exact:open_family_continuous_identity.
Qed.

(** Source for [smooth_compact_domain_inverse]: the inverse
    linear map to the D-to-E inclusion on compact domains,
    supporting the missing zero-dimensional exception in Federer
    4.1.1, p. 344. *)
Definition smooth_compact_domain_inverse:Hom E DT:=
  hom_comp j smooth_compact_domain_fixed_map.

(** Source for [smooth_compact_domain_inverse_evaluation]:
    the inverse preserves the original function, supporting the
    compact-domain correction to Federer 4.1.1, p. 344. *)
Theorem smooth_compact_domain_inverse_evaluation f:
  inc (smooth_compact_domain_inverse f)=f.
Proof.
rewrite /smooth_compact_domain_inverse hom_compE smooth_test_step_evaluation.
exact:smooth_compact_domain_fixed_evaluation.
Qed.

(** Source for [smooth_compact_domain_inverse_continuous]:
    the inverse to inclusion is continuous for Federer's literal
    final topology, supporting the compact-domain correction
    to 4.1.1, p. 344. *)
Theorem smooth_compact_domain_inverse_continuous:
  open_family_continuous EO SO smooth_compact_domain_inverse.
Proof.
exact:(open_family_continuous_compose smooth_compact_domain_fixed_continuous
  (final_open_topology_inclusion (smooth_test_final_topology_laws hE hD) K)).
Qed.

(** Source for [smooth_compact_domain_homeomorphism]: D and E
    have mutually inverse continuous linear maps on every compact
    open domain, refuting the printed nonembedding assertion in
    Federer 4.1.1, p. 344, when the source dimension is zero. *)
Theorem smooth_compact_domain_homeomorphism:
  open_family_continuous SO EO inc /\
  open_family_continuous EO SO smooth_compact_domain_inverse /\
  cancel smooth_compact_domain_inverse inc /\ cancel inc smooth_compact_domain_inverse.
Proof.
split; first exact:smooth_test_inclusion_continuous.
split; first exact:smooth_compact_domain_inverse_continuous.
split; first exact:smooth_compact_domain_inverse_evaluation.
move=>f; apply:(subspace_representation_injective (smooth_test_space_laws hE)).
exact:smooth_compact_domain_inverse_evaluation.
Qed.
End CompactDomain.

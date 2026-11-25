(** Federer (1969), 4.1.8, p. 360: on
    the original slice operator is continuous for the literal
    final topologies of the actual test spaces. The proof first
    corestricts each support step to the second projected support
    and then applies the final-topology mapping law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap AlternatingForms
  CurrentSpaces SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology SmoothFunctionSeminormFamily DirectedSeminormFamilyUP
  SeminormFamilyRestriction SeminormFamilyLinearContinuity LinearSubspaceRepresentationUP
  OpenFamilyTopologyUP CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceSeminormBound CurrentCartesianSliceStepSmooth
  LinearSubspaceLiftSealed SmoothTestSubspaces CurrentCartesianCompactProjections
  CurrentCartesianSliceFieldSupport InitialOpenTopologyUP FinalOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceContinuity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation hDC := (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation hDB := (@current_smooth_derivative_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).

(** Source for [current_cartesian_slice_fixed_step_continuous]:
    continuity of the original slice on each D_K, supporting
    Federer 4.1.8, p. 360. Its image lies in the actual
    fixed second-projection support step; no joint vector
    continuity of the literal final topology is asserted. *)
Theorem current_cartesian_slice_fixed_step_continuous
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB):
  open_family_continuous (smooth_test_step_opens hEC hDC K)
    (@current_test_opens R h2 n B hB j)
    (fun f:smooth_fixed_test_space hEC K=>H S (smooth_test_step hEC K f)).
Proof.
have [KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
pose DK:=smooth_fixed_test_space hEC K.
pose BK:=smooth_fixed_test_space hEB KB.
pose kB:=smooth_fixed_test_inclusion hEB KB.
pose raw:=hom_comp (smooth_test_inclusion hEB) (hom_comp (H S) (smooth_test_step hEC K)).
have hMember f:smooth_fixed_support_subspace hEB KB (raw f).
  have hSupport:@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC (smooth_test_step hEC K f)) `<=` smooth_compact_carrier K.
    rewrite smooth_test_step_evaluation.
    exact:(subspace_representation_member (smooth_fixed_test_space_laws hEC K) f).
  exact:(@current_cartesian_slice_field_fixed_support R h2 m n i j A B hA hB S K KB
    (smooth_test_step hEC K f) (raw f) hKB hSupport
    (@CartesianSlice.laws R h2 m n i j A B hA hB S (smooth_test_step hEC K f))).
pose lift:=@LinearSubspaceLift.map R DK BK EB
  (smooth_fixed_support_subspace hEB KB) kB (smooth_fixed_test_space_laws hEB KB) raw hMember.
have hLift f:kB (lift f)=raw f.
  exact:(@LinearSubspaceLift.evaluation R DK BK EB
    (smooth_fixed_support_subspace hEB KB) kB (smooth_fixed_test_space_laws hEB KB) raw hMember f).
have hContinuous:open_family_continuous (smooth_test_step_opens hEC hDC K)
    (smooth_test_step_opens hEB hDB KB) lift.
  apply:(@initial_open_topology_mapping BK EB DK
    (smooth_function_opens hDB) kB (smooth_test_step_opens hEB hDB KB)
    (smooth_test_step_opens hEC hDC K) lift
    (smooth_test_step_relative_topology hEB hDB KB)).2.
  have he:(fun f=>kB (lift f))=(fun f=>raw f).
    apply:funext=>f;exact:hLift.
  rewrite he.
  exact:(@current_cartesian_slice_step_smooth_continuous R h2 m n i j A B hA hB S K).
have hFactor:(fun f=>H S (smooth_test_step hEC K f))=
    (fun f=>smooth_test_step hEB KB (lift f)).
  apply:funext=>f;apply:(subspace_representation_injective (smooth_test_space_laws hEB)).
  rewrite smooth_test_step_evaluation hLift.
  reflexivity.
rewrite hFactor.
exact:(@open_family_continuous_compose DK BK DB
  (smooth_test_step_opens hEC hDC K) (smooth_test_step_opens hEB hDB KB)
  (@current_test_opens R h2 n B hB j) lift (smooth_test_step hEB KB) hContinuous
  (@final_open_topology_inclusion (smooth_compact_set hNY B)
    (fun L=>smooth_fixed_test_space hEB L) DB (smooth_test_step_opens hEB hDB)
    (fun L f=>smooth_test_step hEB L f) (@current_test_opens R h2 n B hB j)
    (smooth_test_final_topology_laws hEB hDB) KB)).
Qed.

(** Source for [current_cartesian_slice_continuous]: the original
    map phi to phi_S is continuous D^(i+j)(A x B) to D^j(B),
    supporting Federer 4.1.8, p. 360. The proof uses the
    literal final topology and every original fixed-support step;
    it assumes neither joint vector continuity nor S=T. *)
Theorem current_cartesian_slice_continuous (S:@current_space R h2 m A hA i):
  open_family_continuous (@current_test_opens R h2 (m+n) AB hAB (i+j))
    (@current_test_opens R h2 n B hB j) (H S).
Proof.
apply:(@final_open_topology_mapping (smooth_compact_set hNZ AB)
  (fun K=>smooth_fixed_test_space hEC K) DC DB
  (smooth_test_step_opens hEC hDC) (fun K f=>smooth_test_step hEC K f)
  (@current_test_opens R h2 (m+n) AB hAB (i+j)) (@current_test_opens R h2 n B hB j)
  (H S) (smooth_test_final_topology_laws hEC hDC)).2=>K.
exact:(@current_cartesian_slice_fixed_step_continuous S K).
Qed.
End CurrentCartesianSliceContinuity.

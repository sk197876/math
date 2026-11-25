(** Federer (1969), 4.1.8, p. 360: on
    the displayed iterated action T(phi_S) is an actual
    continuous current for arbitrary original factors. Existence
    follows from the already proved literal-test-topology
    continuity of the original linear slice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap AlternatingForms
  CurrentSpaces SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology SmoothFunctionSeminormFamily DirectedSeminormFamilyUP
  SeminormFamilyRestriction SeminormFamilyLinearContinuity LinearSubspaceRepresentationUP
  OpenFamilyTopologyUP CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceContinuity ContinuousRealDual NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceFunctionalExistence.
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

(** Source for [current_cartesian_slice_functional_exists]:
    the original formula (S x T)(phi)=T(phi_S),
    Federer 4.1.8, p. 360, defines an actual continuous
    current on A x B. No product-current or mixed-degree
    density theorem is assumed. *)
Theorem current_cartesian_slice_functional_exists
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  exists P:@current_space R h2 (m+n) AB hAB (i+j),forall phi:DC,
    @current_value R h2 (m+n) AB hAB (i+j) P phi=
    @current_value R h2 n B hB j T (H S phi).
Proof.
pose O:=@current_test_opens R h2 (m+n) AB hAB (i+j).
pose hO:=(smooth_test_final_topology_laws hEC hDC).1.
pose L:=hom_comp (@current_value R h2 n B hB j T) (H S).
have hContinuous:open_family_continuous O
    (norm_open_family (@scalar_absolute_value_norm R)) L.
  exact:(open_family_continuous_compose
    (@current_cartesian_slice_continuous R h2 m n i j A B hA hB S)
    (@continuous_real_dual_member_continuous R DB
      (@current_test_opens R h2 n B hB j) (smooth_test_final_topology_laws hEB hDB).1 T)).
have [P hP]:=@continuous_real_dual_represents R DC O hO L hContinuous.
exists P=>phi.
exact:(congr1 (fun f:Hom DC R^o=>f phi) hP).
Qed.

(** Source for [current_cartesian_slice_functional_unique]:
    the original iterated action specifies at most one actual
    current, supporting Federer 4.1.8, p. 360. This
    supporting uniqueness concerns all tests; the original
    separated-test characterization is proved separately. *)
Theorem current_cartesian_slice_functional_unique
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j)
    (P Q:@current_space R h2 (m+n) AB hAB (i+j)):
  (forall phi:DC,@current_value R h2 (m+n) AB hAB (i+j) P phi=
    @current_value R h2 n B hB j T (H S phi))->
  (forall phi:DC,@current_value R h2 (m+n) AB hAB (i+j) Q phi=
    @current_value R h2 n B hB j T (H S phi))->P=Q.
Proof.
move=>hP hQ.
apply:(subspace_representation_injective
  (@continuous_real_dual_model_laws R DC (@current_test_opens R h2 (m+n) AB hAB (i+j))
    (smooth_test_final_topology_laws hEC hDC).1)).
apply:hom_ext=>phi.
by rewrite hP hQ.
Qed.
End CurrentCartesianSliceFunctionalExistence.

(** Federer (1969), 4.1.8, p. 360: on
    each original fixed-support step, the slice is continuous
    into the actual smooth-form space. The proof applies
    the original derivative-seminorm mapping criterion to the
    already proved same-support estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap AlternatingForms
  CurrentSpaces SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology SmoothFunctionSeminormFamily DirectedSeminormFamilyUP
  SeminormFamilyRestriction SeminormFamilyLinearContinuity LinearSubspaceRepresentationUP
  OpenFamilyTopologyUP CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceSeminormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceStepSmooth.
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

(** Source for [current_cartesian_slice_step_smooth_continuous]:
    the original linear slice on D_K is continuous
    into E^j(B), supporting Federer 4.1.8, p. 360.
    This is proved from the actual input seminorm bounds;
    no vector continuity of the final test topology is used. *)
Theorem current_cartesian_slice_step_smooth_continuous
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB):
  open_family_continuous (smooth_test_step_opens hEC hDC K)
    (smooth_function_opens hDB)
    (fun f:smooth_fixed_test_space hEC K=>
      smooth_test_inclusion hEB (H S (smooth_test_step hEC K f))).
Proof.
pose DK:=smooth_fixed_test_space hEC K.
pose inclusion:=smooth_fixed_test_inclusion hEC K.
pose IA:=(nat*smooth_compact_set hNZ AB)%type.
pose IB:=(nat*smooth_compact_set hNY B)%type.
pose p:=fun (a:IA) (f:DK)=>smooth_function_derivative_seminorm hDC a.2 a.1 (inclusion f).
pose q:=fun (a:IB) (g:EB)=>smooth_function_derivative_seminorm hDB a.2 a.1 g.
pose raw:=hom_comp (smooth_test_inclusion hEB) (hom_comp (H S) (smooth_test_step hEC K)).
have hp:is_directed_seminorm_family p.
  exact:(@restricted_seminorm_family_directed R EC DK IA
    (fun (a:IA) (g:EC)=>smooth_function_derivative_seminorm hDC a.2 a.1 g)
    (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hDC)) inclusion).
change (open_family_continuous (smooth_test_step_opens hEC hDC K) (smooth_function_opens hDB) raw).
apply:(@seminorm_family_bounded_linear_continuous R DK EB IA IB p q
  (smooth_test_step_opens hEC hDC K) (smooth_function_opens hDB) hp
  (smooth_test_step_topology_laws hEC hDC K) (smooth_function_topology_laws hDB) raw).
move=>[order L].
have[r [M [hM hBound]]]:=@current_cartesian_slice_seminorm_bound R h2 m n i j A B hA hB S K order.
exists (r,K),M;split;first exact:hM.
move=>f.
have hSupport:@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC (smooth_test_step hEC K f)) `<=` smooth_compact_carrier K.
  rewrite smooth_test_step_evaluation.
  exact:(subspace_representation_member (smooth_fixed_test_space_laws hEC K) f).
have hEstimate:=@hBound L (smooth_test_step hEC K f) hSupport.
rewrite smooth_test_step_evaluation in hEstimate.
exact:hEstimate.
Qed.
End CurrentCartesianSliceStepSmooth.

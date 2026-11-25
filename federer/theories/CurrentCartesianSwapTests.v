(** Federer (1969), 4.1.18, p. 374: the
    all-test Cartesian interchange can use genuine compact
    swapped pullbacks. Compactness follows from the old
    continuous inverse swap; no current support or finite
    mass premise is needed.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentCoefficientNorms
  EuclideanCartesianMap EuclideanCartesianSwap EuclideanCartesianSwapLinear
  CurrentCartesianDomain CurrentCartesianSwapDomain SmoothCompactSet
  SmoothCompactImage SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestSubspaces
  SmoothFormPullbackSealed SmoothFormPullbackSupport SmoothFunctionSupport
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSwapTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall x,A x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall x,B x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B x.
Local Notation AB:=(@euclidean_cartesian_set R m n A B).
Local Notation BA:=(@euclidean_cartesian_set R n m B A).
Local Notation hAB:=(@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA:=(@current_cartesian_domain_open R n m B A hB hA).
Local Notation X:=(R_n R (m+n)).
Local Notation Y:=(R_n R (n+m)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (n+m))).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+m))).
Local Notation E:=(@current_smooth_space R h2 (n+m) BA hBA j).
Local Notation F:=(@current_smooth_space R h2 (m+n) AB hAB j).
Local Notation hE:=(@current_smooth_space_laws R h2 (n+m) BA hBA j).
Local Notation hF:=(@current_smooth_space_laws R h2 (m+n) AB hAB j).
Local Notation DT:=(@current_test_space R h2 (n+m) BA hBA j).
Local Notation DS:=(@current_test_space R h2 (m+n) AB hAB j).
Local Notation swap:=(@euclidean_cartesian_swap_map R m n).
Local Notation back:=(@euclidean_cartesian_swap_map R n m).
Local Notation image:=(fun z hz=>@current_cartesian_swap_image R m n A B z hz).
Local Notation backImage:=(fun z hz=>@current_cartesian_swap_image R n m B A z hz).
Local Notation hSmooth:=(@euclidean_cartesian_swap_smooth R m n AB hAB).
Local Notation hBack:=(@euclidean_cartesian_swap_smooth R n m BA hBA).
Local Notation Pull:=(@SmoothFormPullback.operator R h2 (m+n) (n+m) j
  AB BA hAB hBA swap image hSmooth).
Local Notation IncE:=(smooth_test_inclusion hE).
Local Notation IncF:=(smooth_test_inclusion hF).

(** Source for [current_cartesian_swap_pullback_compact]:
    the original inverse interchange carries a compact
    target support to a compact source support, as
    needed for the averaged action in 4.1.18, p. 374. *)
Lemma current_cartesian_swap_pullback_compact (phi:DT):
  smooth_compact_support_subspace hF (Pull (IncE phi)).
Proof.
have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) phi.
pose L:=@smooth_compact_image R Y X NY NX hNY hNX BA AB back
  backImage (norm_class_continuous (hBack 0%N)) K.
exists L=>z hz.
have hPre:=@smooth_form_pullback_support_preimage R h2 (m+n) (n+m) j
  AB BA hAB hBA swap image hSmooth (IncE phi) K hK z hz.
change ((back @` smooth_compact_carrier K) z).
exists (swap z);first exact:hPre.2.
exact:(@euclidean_cartesian_swapK R m n z).
Qed.

(** Source for [current_cartesian_swap_tests]: the compact
    swapped pullback is an actual linear test operator,
    supporting the all-test interchange used in 4.1.18,
    p. 374. The public subspace lift chooses no
    mathematical data beyond the proved compactness law. *)
Definition current_cartesian_swap_tests:Hom DT DS:=
  @LinearSubspaceLift.map R DT DS F (smooth_compact_support_subspace hF)
    IncF (smooth_test_space_laws hF) (hom_comp Pull IncE)
    current_cartesian_swap_pullback_compact.

(** Source for [current_cartesian_swap_tests_inclusion]:
    exact agreement with the original smooth pullback,
    supporting the first display of 4.1.18, p. 374. *)
Theorem current_cartesian_swap_tests_inclusion phi:
  IncF (current_cartesian_swap_tests phi)=Pull (IncE phi).
Proof.
exact:LinearSubspaceLift.evaluation.
Qed.
End CurrentCartesianSwapTests.

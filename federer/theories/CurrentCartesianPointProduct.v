(** Federer (1969), 4.1.8, p. 362: the
    original point product is the point-inclusion
    pushforward. The already proved all-test slice
    identity supplies an actual compact pullback
    replacement for every target test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  AlternatingForms CurrentSpaces CurrentEvaluation CurrentDirac CurrentCartesianDomain
  CurrentCartesianSliceSealed CurrentCartesianPointInclusion CurrentCartesianPointInclusionProper
  CurrentCartesianPointSlice CurrentCartesianProductSealed CurrentCartesianProductAction
  CurrentPushforwardUP CurrentPushforwardSealed CurrentProperSupport
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variable z:X.
Hypothesis hz:A z.
Variable T:@current_space R h2 n B hB j.
Local Notation f := (@current_cartesian_point_inclusion R m n z).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n A B z hz y hy).
Local Notation hSmooth := (@current_cartesian_point_inclusion_smooth R m n B hB z).
Local Notation hProper := (@current_cartesian_point_inclusion_proper R h2 m n j A B hA hB z hz T).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB j).
Local Notation IC := (smooth_test_inclusion hEC).
Local Notation tb := (@current_test_value R h2 n B hB j).
Local Notation pull := (@SmoothFormPullback.operator R h2 n (m+n) j B AB hB hAB f Image hSmooth).

(** Source for [current_cartesian_point_pushforward]: the
    original epsilon_z#T using the actual sealed
    pushforward and proved support properness, supporting
    Federer 4.1.8, p. 362. *)
Definition current_cartesian_point_pushforward:@current_space R h2 (m+n) AB hAB j:=
  @CurrentPushforward.value R h2 n (m+n) j B AB hB hAB T f Image hSmooth hProper.

(** Source for [current_cartesian_point_pushforward_action]:
    an actual compact test agreeing with the original
    point-inclusion pullback computes its pushforward,
    supporting Federer 4.1.8, p. 362. *)
Theorem current_cartesian_point_pushforward_action phi psi:
  (forall y,B y->tb psi y=vb (pull (IC phi)) y)->
  @current_value R h2 (m+n) AB hAB j current_cartesian_point_pushforward phi=
    @current_value R h2 n B hB j T psi.
Proof.
move=>hPoint.
apply:(@CurrentPushforward.laws R h2 n (m+n) j B AB hB hAB T f Image hSmooth hProper phi psi).
exists B;split.
- rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY B y).1 (@hB y hy).
- split;first by move=>y hy;exact:hy.1.
  split;first by move=>y hy;exact:hy.
  exact:hPoint.
Qed.

(** Source for [current_cartesian_point_product]:
    delta_z times T=epsilon_z#T, the original
    point-product identity in Federer 4.1.8, p. 362.
    T is an arbitrary actual current; no integration
    representation or compact support is assumed. *)
Theorem current_cartesian_point_product:
  @CartesianCurrentProduct.value R h2 m n 0%N j A B hA hB
    (@dirac_current R h2 m A hA z) T=current_cartesian_point_pushforward.
Proof.
apply:(@current_values_extensional R h2 (m+n) j AB hAB)=>phi.
rewrite current_cartesian_product_action.
apply:esym;apply:current_cartesian_point_pushforward_action=>b hb.
exact:(@current_cartesian_point_slice R h2 m n j A B hA hB z hz phi b hb).
Qed.
End CurrentCartesianPointProduct.

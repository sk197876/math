(** Federer (1969), 4.1.8, p. 360: on
    the original product is uniquely determined by
    its complete mixed-degree separated-test characterisation.
    The original full-space tensor density is used only after
    actual compact localization to the original open product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap AlternatingForms
  CurrentSpaces SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology SmoothFunctionSeminormFamily DirectedSeminormFamilyUP
  SeminormFamilyRestriction SeminormFamilyLinearContinuity LinearSubspaceRepresentationUP
  OpenFamilyTopologyUP CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceContinuity ContinuousRealDual NormOpenTopology
  CurrentCartesianSliceFunctionalExistence CurrentCartesianSeparatedSlice CurrentCartesianProductUP
  CurrentCartesianTestProductSealed CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentCartesianMixedAnnihilator CurrentEvaluation CurrentPointEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianProductUnique.
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

Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
(** Source for [current_cartesian_product_unique]: the original
    product current is unique under both complete separated-test
    equations, Federer 4.1.8, p. 360. The proof retains
    every mixed degree and uses the original open-product
    annihilator theorem derived from 4.1.3. *)
Theorem current_cartesian_product_unique
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j)
    (P Q:@current_space R h2 (m+n) AB hAB (i+j)):
  @is_current_cartesian_product R h2 m n A B hA hB Pure i j S T P->
  @is_current_cartesian_product R h2 m n A B hA hB Pure i j S T Q->P=Q.
Proof.
move=>hP hQ.
have hEqual:forall k l (e:(k+l)%N=(i+j)%N)
    (a:@current_test_space R h2 m A hA k) (b:@current_test_space R h2 n B hB l),
    @current_value R h2 (m+n) AB hAB (i+j) P
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b))=
    @current_value R h2 (m+n) AB hAB (i+j) Q
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b)).
  move=>k l e a b.
  case:(pselect (k = i))=>[hk|hk].
  - subst k.
    have hl:l=j.
      apply/eqP.
      have heq:(i+l == i+j)%N:=introT eqP e.
      by rewrite eqn_add2l in heq.
    subst l.
    by rewrite current_test_degree_transport_identity hP.1 hQ.1.
  - by rewrite (hP.2 k l e hk a b) (hQ.2 k l e hk a b).
have hZero:forall k l (e:(k+l)%N=(i+j)%N)
    (a:@current_test_space R h2 m A hA k) (b:@current_test_space R h2 n B hB l),
    @current_value R h2 (m+n) AB hAB (i+j) (P-Q)
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b))=0.
  move=>k l e a b.
  change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB
    (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b)) (P-Q)=0).
  by rewrite (linB (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB
    (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b)))) P Q)
    !current_point_evaluation_values hEqual subrr.
have hAll:=@current_cartesian_mixed_annihilator_zero R h2 m n (i+j) A B hA hB (P-Q) hZero.
apply:(@current_values_extensional R h2 (m+n) (i+j) AB hAB)=>phi.
have hValue:=hAll phi.
change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB phi (P-Q)=0) in hValue.
rewrite (linB (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB phi)) P Q)
  !current_point_evaluation_values in hValue.
apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hValue.
Qed.
End CurrentCartesianProductUnique.

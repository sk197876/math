(** Federer (1969), 4.1.8, p. 361: pullback
    by the original natural association identifies the
    two actual triple separated tests. The proof uses
    the existing coordinate-list identification and original
    associative exterior product, including every zero degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanDimensionCastLinear EuclideanCartesianReassociation
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentTestValueLaws CurrentDegreeTransport SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentCartesianDomain CurrentCartesianReassociationDomain CurrentCartesianTestProductSealed
  CovectorCartesianReassociation FormReindexPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianReassociationPurePullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)) (C:set (R_n R v)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Hypothesis hC:forall c,C c->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) C c.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BC := (@euclidean_cartesian_set R n v B C).
Local Notation Left := (@euclidean_cartesian_set R (m+n) v AB C).
Local Notation Right := (@euclidean_cartesian_set R m (n+v) A BC).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBC := (@current_cartesian_domain_open R n v B C hB hC).
Local Notation hLeft := (@current_cartesian_domain_open R (m+n) v AB C hAB hC).
Local Notation hRight := (@current_cartesian_domain_open R m (n+v) A BC hA hBC).
Local Notation assoc := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v))).
Local Notation Image := (fun z hz=>@current_cartesian_reassociation_image R m n v A B C z hz).
Local Notation hSmooth := (@euclidean_dimension_cast_smooth R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v)) Left hLeft).
Local Notation pLeft := (@euclidean_first_block_map R (m+n) v).
Local Notation qLeft := (@euclidean_last_block_map R (m+n) v).
Local Notation qRight := (@euclidean_last_block_map R m (n+v)).
Local Notation EL := (fun d=>@current_smooth_space R h2 ((m+n)+v) Left hLeft d).
Local Notation ER := (fun d=>@current_smooth_space R h2 (m+(n+v)) Right hRight d).
Local Notation vl := (fun d=>@current_smooth_value R h2 ((m+n)+v) Left hLeft d).
Local Notation vr := (fun d=>@current_smooth_value R h2 (m+(n+v)) Right hRight d).
Local Notation hEL := (fun d=>@current_smooth_space_laws R h2 ((m+n)+v) Left hLeft d).
Local Notation hER := (fun d=>@current_smooth_space_laws R h2 (m+(n+v)) Right hRight d).
Local Notation IL := (fun d=>smooth_test_inclusion (hEL d)).
Local Notation IR := (fun d=>smooth_test_inclusion (hER d)).
Local Notation PureAB := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation PureBC := (fun l r=>@CartesianTestProduct.value R h2 n v B C hB hC l r).
Local Notation PureL := (fun t r=>@CartesianTestProduct.value R h2 (m+n) v AB C hAB hC t r).
Local Notation PureR := (fun k t=>@CartesianTestProduct.value R h2 m (n+v) A BC hA hBC k t).
Local Notation TrL := (fun a b (e:a=b)=>@current_test_degree_transport R h2 ((m+n)+v) Left hLeft a b e).
Local Notation TrR := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+(n+v)) Right hRight a b e).
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 ((m+n)+v) (m+(n+v)) d
  Left Right hLeft hRight assoc Image hSmooth).

(** Source for [current_cartesian_reassociation_pure_pullback]:
    the original natural association pulls alpha times
    (beta times gamma) back to (alpha times beta)
    times gamma with only the equal-degree identification,
    supporting Federer 4.1.8, p. 361. Both
    sides are the actual smooth representatives of compact tests. *)
Theorem current_cartesian_reassociation_pure_pullback d k l r (e:(k+(l+r))%N=d)
    (alpha:@current_test_space R h2 m A hA k)
    (beta:@current_test_space R h2 n B hB l)
    (gamma:@current_test_space R h2 v C hC r):
  pull d (IR d (TrR _ _ e (PureR k (l+r) alpha (PureBC l r beta gamma))))=
    IL d (TrL _ _ (eq_trans (esym (addnA k l r)) e)
      (PureL (k+l) r (PureAB k l alpha beta) gamma)).
Proof.
apply:(smooth_function_extensional (hEL d))=>z hz.
have hTarget:=@current_cartesian_reassociation_image R m n v A B C z hz.
have hInnerTarget:=(@CartesianTestProduct.laws R h2 n v B C hB hC l r).2
  beta gamma (qRight (assoc z)) hTarget.2.
have hOuterTarget:=(@CartesianTestProduct.laws R h2 m (n+v) A BC hA hBC k (l+r)).2
  alpha (PureBC l r beta gamma) (assoc z) hTarget.
rewrite hInnerTarget euclidean_cartesian_reassociate_first euclidean_cartesian_reassociate_middle
  euclidean_cartesian_reassociate_last in hOuterTarget.
have hTargetTr:=@current_test_degree_transport_values R h2 (m+(n+v)) Right hRight (k+(l+r)) d e
  (PureR k (l+r) alpha (PureBC l r beta gamma)) (assoc z).
rewrite hOuterTarget in hTargetTr.
have hPull:=@smooth_form_pullback_values R ((m+n)+v) (m+(n+v)) d Left Right
  (ER d) (EL d) (vr d) (vl d) assoc (pull d)
  (@SmoothFormPullback.laws R h2 ((m+n)+v) (m+(n+v)) d Left Right hLeft hRight assoc Image hSmooth)
  (IR d (TrR _ _ e (PureR k (l+r) alpha (PureBC l r beta gamma)))) z assoc hz
  (@euclidean_dimension_cast_differential R ((m+n)+v)%N (m+(n+v))%N
    (esym (addnA m n v)) Left hLeft z hz).
have hLeftValue:=eq_trans hPull
  (congr1 (fun a:A_m (R_n R (m+(n+v))) R^o d=>A_m_dual (hom_as_linear assoc) a) hTargetTr).
have hInnerSource:=(@CartesianTestProduct.laws R h2 m n A B hA hB k l).2
  alpha beta (pLeft z) hz.1.
have hOuterSource:=(@CartesianTestProduct.laws R h2 (m+n) v AB C hAB hC (k+l) r).2
  (PureAB k l alpha beta) gamma z hz.
rewrite hInnerSource in hOuterSource.
have hSourceTr:=@current_test_degree_transport_values R h2 ((m+n)+v) Left hLeft ((k+l)+r) d
  (eq_trans (esym (addnA k l r)) e) (PureL (k+l) r (PureAB k l alpha beta) gamma) z.
rewrite hOuterSource in hSourceTr.
rewrite original_linear_pullback_reindex covector_cartesian_reassociation_product in hLeftValue.
cbn beta in hLeftValue, hSourceTr.
rewrite form_reindex_composition in hLeftValue.
exact:(eq_trans hLeftValue (esym hSourceTr)).
Qed.
End CurrentCartesianReassociationPurePullback.

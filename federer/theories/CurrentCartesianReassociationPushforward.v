(** Federer (1969), 4.1.8, p. 361: pullback
    by the original natural association identifies the
    two actual triple separated tests. The proof uses
    the existing coordinate-list identification and original
    associative exterior product, including every zero degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanDimensionCastLinear EuclideanCartesianReassociation
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentTestValueLaws CurrentDegreeTransport SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentCartesianDomain CurrentCartesianReassociationDomain CurrentCartesianTestProductSealed
  CovectorCartesianReassociation FormReindexPullback CurrentCartesianReassociationPurePullback
  CurrentCartesianProductSealed CurrentPushforwardSealed CurrentPushforwardUP
  NormMetric NormOpenTopology NormBoundedLinearTopology CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianReassociationPushforward.
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

Local Notation CL := (fun d=>@current_space R h2 ((m+n)+v) Left hLeft d).
Local Notation CR := (fun d=>@current_space R h2 (m+(n+v)) Right hRight d).
Local Notation ProductAB := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation ProductL := (fun t k=>@CartesianCurrentProduct.value R h2 (m+n) v t k AB C hAB hC).
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_reassociated_current]: the
    original pushforward by natural association in Federer
    4.1.8, p. 361, using the earlier sealed
    pushforward and proved properness on the actual support. *)
Definition current_cartesian_reassociated_current d (Curr:CL d):CR d:=
  @CurrentPushforward.value R h2 ((m+n)+v) (m+(n+v)) d Left Right hLeft hRight Curr
    assoc Image hSmooth
    (@current_cartesian_reassociation_proper_on_support R m n v A B C h2 hA hB hC d Curr).

(** Source for [current_cartesian_reassociation_action]: every
    actual compact test agreeing with the original pullback
    gives the original reassociation pushforward action, supporting
    Federer 4.1.8, p. 361. *)
Theorem current_cartesian_reassociation_action d (Curr:CL d)
    (phi:@current_test_space R h2 (m+(n+v)) Right hRight d)
    (psi:@current_test_space R h2 ((m+n)+v) Left hLeft d):
  (forall z,Left z->@current_test_value R h2 ((m+n)+v) Left hLeft d psi z=
    vl d (pull d (IR d phi)) z)->
  @current_value R h2 (m+(n+v)) Right hRight d (current_cartesian_reassociated_current Curr) phi=
    @current_value R h2 ((m+n)+v) Left hLeft d Curr psi.
Proof.
move=>hPoint.
apply:(@CurrentPushforward.laws R h2 ((m+n)+v) (m+(n+v)) d Left Right hLeft hRight Curr
  assoc Image hSmooth
  (@current_cartesian_reassociation_proper_on_support R m n v A B C h2 hA hB hC d Curr) phi psi).
exists Left;split.
- rewrite openE=>z hz.
  exact:(@norm_domain_interior_neighbourhood R (R_n R ((m+n)+v))
    (inner_norm (@euclidean_inner_productP R ((m+n)+v)))
    (inner_norm_real_norm (@euclidean_inner_productP R ((m+n)+v))) Left z).1 (@hLeft z hz).
- split;first by move=>z hz;exact:hz.1.
  split;first by move=>z hz;exact:hz.
  exact:hPoint.
Qed.

(** Source for [current_cartesian_reassociation_mixed_action]:
    the original association pushforward on every triple
    separated test is exactly its other associated test
    action, supporting the associativity assertion in Federer
    4.1.8, p. 361, with every mixed degree retained. *)
Theorem current_cartesian_reassociation_mixed_action i j k
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j)
    (U:@current_space R h2 v C hC k) a b c (e:(a+(b+c))%N=((i+j)+k)%N)
    (alpha:@current_test_space R h2 m A hA a)
    (beta:@current_test_space R h2 n B hB b)
    (gamma:@current_test_space R h2 v C hC c):
  @current_value R h2 (m+(n+v)) Right hRight ((i+j)+k)
    (current_cartesian_reassociated_current (ProductL (i+j) k (ProductAB i j S T) U))
    (TrR _ _ e (PureR a (b+c) alpha (PureBC b c beta gamma)))=
  @current_value R h2 ((m+n)+v) Left hLeft ((i+j)+k) (ProductL (i+j) k (ProductAB i j S T) U)
    (TrL _ _ (eq_trans (esym (addnA a b c)) e)
      (PureL (a+b) c (PureAB a b alpha beta) gamma)).
Proof.
have hPull:=@current_cartesian_reassociation_pure_pullback R h2 m n v A B C hA hB hC
  ((i+j)+k) a b c e alpha beta gamma.
have hPoint z (hz:Left z):
    @current_test_value R h2 ((m+n)+v) Left hLeft ((i+j)+k)
      (TrL _ _ (eq_trans (esym (addnA a b c)) e)
        (PureL (a+b) c (PureAB a b alpha beta) gamma)) z=
    vl ((i+j)+k) (pull ((i+j)+k) (IR ((i+j)+k)
      (TrR _ _ e (PureR a (b+c) alpha (PureBC b c beta gamma))))) z.
  exact:(esym (congr1 (fun f:EL ((i+j)+k)=>vl ((i+j)+k) f z) hPull)).
exact:(@current_cartesian_reassociation_action ((i+j)+k) (ProductL (i+j) k (ProductAB i j S T) U)
  (TrR _ _ e (PureR a (b+c) alpha (PureBC b c beta gamma)))
  (TrL _ _ (eq_trans (esym (addnA a b c)) e) (PureL (a+b) c (PureAB a b alpha beta) gamma)) hPoint).
Qed.
End CurrentCartesianReassociationPushforward.

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
  NormMetric NormOpenTopology NormBoundedLinearTopology CurrentSupportGeometry
  CurrentCartesianReassociationPushforward CurrentCartesianTripleExtensional
  CurrentCartesianProductIdentifiedAction CurrentDegreeTransportComposition CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianProductAssociative.
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

Local Notation ProductBC := (fun j k=>@CartesianCurrentProduct.value R h2 n v j k B C hB hC).
Local Notation ProductR := (fun i t=>@CartesianCurrentProduct.value R h2 m (n+v) i t A BC hA hBC).
Local Notation AssocC := (fun d Curr=>@current_cartesian_reassociated_current R h2 m n v A B C hA hB hC d Curr).
Local Notation CTrR := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+(n+v)) Right hRight a b e).

(** Source for [current_cartesian_product_associative]: the
    original Cartesian product of currents is associative,
    Federer 4.1.8, p. 361, through the natural
    original coordinate and equal-degree identifications. The
    proof uses all triple mixed test degrees and the
    earlier density theorem, without representation by measure. *)
Theorem current_cartesian_product_associative i j k
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j)
    (U:@current_space R h2 v C hC k):
  CTrR _ _ (esym (addnA i j k))
    (AssocC ((i+j)+k) (ProductL (i+j) k (ProductAB i j S T) U))=
    ProductR i (j+k) S (ProductBC j k T U).
Proof.
apply:(@current_cartesian_triple_values_extensional R h2 m n v A B C hA hB hC (i+(j+k))).
move=>a b c e alpha beta gamma.
cbn beta.
rewrite (@current_degree_transport_evaluation R h2 (m+(n+v)) Right hRight ((i+j)+k) (i+(j+k))
  (esym (addnA i j k)) (AssocC ((i+j)+k) (ProductL (i+j) k (ProductAB i j S T) U))
  (TrR _ _ e (PureR a (b+c) alpha (PureBC b c beta gamma))))
  current_test_degree_transport_composition.
rewrite (@current_cartesian_reassociation_mixed_action R h2 m n v A B C hA hB hC
  i j k S T U a b c (eq_trans e (esym (esym (addnA i j k)))) alpha beta gamma).
pose g:((a+b)+c)%N=((i+j)+k)%N:=
  eq_trans (esym (addnA a b c)) (eq_trans e (esym (esym (addnA i j k)))).
change (@current_value R h2 ((m+n)+v) Left hLeft ((i+j)+k)
    (ProductL (i+j) k (ProductAB i j S T) U)
    (TrL _ _ g (PureL (a+b) c (PureAB a b alpha beta) gamma))=
  @current_value R h2 (m+(n+v)) Right hRight (i+(j+k))
    (ProductR i (j+k) S (ProductBC j k T U))
    (TrR _ _ e (PureR a (b+c) alpha (PureBC b c beta gamma)))).
case:(pselect (a = i))=>ha.
- subst a.
  have hBCDegree:(b+c)%N=(j+k)%N.
    apply/eqP;have heq:(i+(b+c) == i+(j+k))%N:=introT eqP e.
    by rewrite eqn_add2l in heq.
  case:(pselect (b = j))=>hb.
  + subst b.
    have hc:c=k.
      apply/eqP;have heq:(j+c == j+k)%N:=introT eqP hBCDegree.
      by rewrite eqn_add2l in heq.
    subst c.
    rewrite !current_test_degree_transport_identity
      ((@CartesianCurrentProduct.laws R h2 (m+n) v (i+j) k AB C hAB hC
        (ProductAB i j S T) U).1 (PureAB i j alpha beta) gamma)
      ((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).1 alpha beta)
      ((@CartesianCurrentProduct.laws R h2 m (n+v) i (j+k) A BC hA hBC
        S (ProductBC j k T U)).1 alpha (PureBC j k beta gamma))
      ((@CartesianCurrentProduct.laws R h2 n v j k B C hB hC T U).1 beta gamma).
    by rewrite mulrA.
  + have hPair:(i+b)%N<>(i+j)%N.
      move=>hSum;apply:hb;apply/eqP.
      have heq:(i+b == i+j)%N:=introT eqP hSum.
      by rewrite eqn_add2l in heq.
    have hSource:=(@CartesianCurrentProduct.laws R h2 (m+n) v (i+j) k AB C hAB hC
      (ProductAB i j S T) U).2 (i+b) c g hPair (PureAB i b alpha beta) gamma.
    have hRight:=@current_cartesian_product_identified_action R h2 m (n+v) A BC hA hBC
      i (j+k) S (ProductBC j k T U) i (b+c) e (erefl i) hBCDegree alpha (PureBC b c beta gamma).
    rewrite current_test_degree_transport_identity in hRight.
    have hInner:=(@CartesianCurrentProduct.laws R h2 n v j k B C hB hC T U).2
      b c hBCDegree hb beta gamma.
    by rewrite hSource hRight hInner mulr0.
- have hRight:=(@CartesianCurrentProduct.laws R h2 m (n+v) i (j+k) A BC hA hBC
    S (ProductBC j k T U)).2 a (b+c) e ha alpha (PureBC b c beta gamma).
  case:(pselect ((a+b)%N=(i+j)%N))=>hPair.
  + have hc:c=k.
      apply/eqP.
      have hSum:((i+j)+c)%N=((i+j)+k)%N:=
        eq_trans (congr1 (fun r:nat=>(r+c)%N) (esym hPair)) g.
      have heq:((i+j)+c == (i+j)+k)%N:=introT eqP hSum.
      by rewrite eqn_add2l in heq.
    have hSource:=@current_cartesian_product_identified_action R h2 (m+n) v AB C hAB hC
      (i+j) k (ProductAB i j S T) U (a+b) c g hPair hc (PureAB a b alpha beta) gamma.
    have hInner:=(@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).2
      a b hPair ha alpha beta.
    by rewrite hSource hInner hRight mul0r.
  + have hSource:=(@CartesianCurrentProduct.laws R h2 (m+n) v (i+j) k AB C hAB hC
      (ProductAB i j S T) U).2 (a+b) c g hPair (PureAB a b alpha beta) gamma.
    by rewrite hSource hRight.
Qed.
End CurrentCartesianProductAssociative.

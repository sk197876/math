(** Federer (1969), 4.1.8, p. 360: original mixed tests
    and equal-degree identifications for the product formulas.
    All current and test spaces are the actual opaque spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  CurrentCartesianProductTransportedAction CurrentCartesianMixedExtensional
  CurrentCartesianBoundaryTests CurrentBoundary CurrentTestExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianBoundaryPositive.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation CC := (fun r=>@current_space R h2 (m+n) AB hAB r).
Local Notation CA := (fun r=>@current_space R h2 m A hA r).
Local Notation CB := (fun r=>@current_space R h2 n B hB r).
Local Notation ec := (fun r=>@current_value R h2 (m+n) AB hAB r).
Local Notation ea := (fun r=>@current_value R h2 m A hA r).
Local Notation eb := (fun r=>@current_value R h2 n B hB r).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation CTr := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).

Local Notation bdA := (fun r=>@current_boundary R h2 m r A hA).
Local Notation bdB := (fun r=>@current_boundary R h2 n r B hB).
Local Notation bdC := (fun r=>@current_boundary R h2 (m+n) r AB hAB).
Local Notation dA := (fun r=>@current_test_exterior_derivative R h2 m r A hA).
Local Notation dB := (fun r=>@current_test_exterior_derivative R h2 n r B hB).


(** Source for [current_cartesian_boundary_positive]:
    for two positive-degree factors, boundary(S times T)
    equals boundary S times T plus (-1)^degree(S)
    S times boundary T, the first displayed boundary
    formula of Federer 4.1.8, p. 360. Equal
    natural totals use the original degree identifications. *)
Theorem current_cartesian_boundary_positive i j (S:CA i.+1) (T:CB j.+1):
  bdC (i+j.+1) (CTr _ _ (addSn i j.+1) (Product i.+1 j.+1 S T))=
    Product i j.+1 (bdA i S) T+
    (-1:R)^+i.+1*:CTr _ _ (eq_trans (addSn i j) (esym (addnS i j)))
      (Product i.+1 j S (bdB j T)).
Proof.
apply:(@current_cartesian_mixed_values_extensional R h2 m n A B hA hB (i+j.+1)).
move=>k l e a b.
have hLinear (P Q:CC (i+j.+1)) c:
    ec (i+j.+1) (P+c*:Q) (Tr _ _ e (Pure k l a b))=
    ec (i+j.+1) P (Tr _ _ e (Pure k l a b))+
      c*ec (i+j.+1) Q (Tr _ _ e (Pure k l a b)).
  change (@current_point_evaluation R h2 (m+n) (i+j.+1) AB hAB
    (Tr _ _ e (Pure k l a b)) (P+c*:Q)=
    @current_point_evaluation R h2 (m+n) (i+j.+1) AB hAB
      (Tr _ _ e (Pure k l a b)) P+
    c*:@current_point_evaluation R h2 (m+n) (i+j.+1) AB hAB
      (Tr _ _ e (Pure k l a b)) Q).
  by rewrite (linD (hom_linear (@current_point_evaluation R h2 (m+n) (i+j.+1) AB hAB
    (Tr _ _ e (Pure k l a b)))))
    (linZ (hom_linear (@current_point_evaluation R h2 (m+n) (i+j.+1) AB hAB
    (Tr _ _ e (Pure k l a b))))).
cbn beta.
rewrite hLinear (@current_cartesian_boundary_tests R h2 m n A B hA hB (i+j.+1)
  (CTr _ _ (addSn i j.+1) (Product i.+1 j.+1 S T)) k l e a b).
have hNotSucc (q:nat):q.+1<>q.
  by move=>/eqP;rewrite (gtn_eqF (ltnSn q)).
have hNotPrev (q:nat):q<>q.+1.
  by move=>/eqP;rewrite (ltn_eqF (ltnSn q)).
case:(pselect (k = i))=>hk.
- subst k.
  have hl:l=j.+1.
    apply/eqP;have heq:(i+l == i+j.+1)%N:=introT eqP e.
    by rewrite eqn_add2l in heq.
  subst l.
  have hFirst:=@current_cartesian_product_transported_diagonal R h2 m n A B hA hB
    i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1)
    (eq_trans (addSn i j.+1) (congr1 (fun r:nat=>r.+1) e)) S T (dA i a) b.
  have hSecond:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
    i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1) S T i j.+2
    (eq_trans (addnS i j.+1) (congr1 (fun r:nat=>r.+1) e)) (hNotPrev i) a (dB j.+1 b).
  have hRightSecond:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
    i.+1 j (i+j.+1) (eq_trans (addSn i j) (esym (addnS i j)))
    S (bdB j T) i j.+1 e (hNotPrev i) a b.
  rewrite hFirst hSecond hRightSecond !mulr0 !addr0 current_test_degree_transport_identity
    ((@CartesianCurrentProduct.laws R h2 m n i j.+1 A B hA hB (bdA i S) T).1 a b).
  by rewrite (@current_boundary_evaluation R h2 m i A hA S a).
- case:(pselect (k = i.+1))=>hkNext.
  + subst k.
    have hl:l=j.
      apply/eqP.
      have hEq:(i.+1+l)%N=(i.+1+j)%N:=eq_trans e
        (esym (eq_trans (addSn i j) (esym (addnS i j)))).
      have heq:(i.+1+l == i.+1+j)%N:=introT eqP hEq.
      by rewrite eqn_add2l in heq.
    subst l.
    have hFirst:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
      i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1) S T i.+2 j
      (eq_trans (addSn i.+1 j) (congr1 (fun r:nat=>r.+1) e)) (hNotSucc i.+1) (dA i.+1 a) b.
    have hSecond:=@current_cartesian_product_transported_diagonal R h2 m n A B hA hB
      i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1)
      (eq_trans (addnS i.+1 j) (congr1 (fun r:nat=>r.+1) e)) S T a (dB j b).
    have hRightFirst:=(@CartesianCurrentProduct.laws R h2 m n i j.+1 A B hA hB (bdA i S) T).2
      i.+1 j e (hNotSucc i) a b.
    have hRightSecond:=@current_cartesian_product_transported_diagonal R h2 m n A B hA hB
      i.+1 j (i+j.+1) (eq_trans (addSn i j) (esym (addnS i j))) e S (bdB j T) a b.
    rewrite hFirst hSecond hRightFirst hRightSecond !add0r.
    by rewrite (@current_boundary_evaluation R h2 n j B hB T b).
  + have hkSucc:k.+1<>i.+1.
      move=>h;apply:hk;exact:(congr1 predn h).
    have hFirst:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
      i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1) S T k.+1 l
      (eq_trans (addSn k l) (congr1 (fun r:nat=>r.+1) e)) hkSucc (dA k a) b.
    have hSecond:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
      i.+1 j.+1 (i+j.+1).+1 (addSn i j.+1) S T k l.+1
      (eq_trans (addnS k l) (congr1 (fun r:nat=>r.+1) e)) hkNext a (dB l b).
    have hRightFirst:=(@CartesianCurrentProduct.laws R h2 m n i j.+1 A B hA hB (bdA i S) T).2
      k l e hk a b.
    have hRightSecond:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
      i.+1 j (i+j.+1) (eq_trans (addSn i j) (esym (addnS i j)))
      S (bdB j T) k l e hkNext a b.
    by rewrite hFirst hSecond hRightFirst hRightSecond !mulr0 !add0r.
Qed.
End CurrentCartesianBoundaryPositive.

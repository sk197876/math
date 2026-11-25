(** Federer (1969), 4.1.8, p. 360: on
    the displayed iterated action T(phi_S) is an actual
    continuous current for arbitrary original factors. Existence
    follows from the already proved literal-test-topology
    continuity of the original linear slice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentPointEvaluation CurrentDegreeTransport CurrentCartesianDomain CurrentCartesianProductUP
  CurrentCartesianTestProductSealed CurrentCartesianProductSealed CurrentCartesianProductUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianProductBilinear.
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

Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB j).
Local Notation CC := (@current_space R h2 (m+n) AB hAB (i+j)).
Local Notation ea := (@current_value R h2 m A hA i).
Local Notation eb := (@current_value R h2 n B hB j).
Local Notation ec := (@current_value R h2 (m+n) AB hAB (i+j)).
Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
(** Source for [current_cartesian_product_first_linear]: the
    original Cartesian current product is linear in its
    first factor, Federer 4.1.8, p. 361. The
    proof applies both complete mixed-test equations. *)
Theorem current_cartesian_product_first_linear (T:CB) c (S U:CA):
  Product (c*:S+U) T=c*:Product S T+Product U T.
Proof.
apply:(@current_cartesian_product_unique R h2 m n i j A B hA hB (c*:S+U) T
  (Product (c*:S+U) T) (c*:Product S T+Product U T)).
- exact:(@CartesianCurrentProduct.laws R h2 m n i j A B hA hB (c*:S+U) T).
- have hST:=@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T.
  have hUT:=@CartesianCurrentProduct.laws R h2 m n i j A B hA hB U T.
  split.
  + move=>a b.
    change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB (Pure i j a b)
      (c*:Product S T+Product U T)=ea (c*:S+U) a*eb T b).
    rewrite (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB (Pure i j a b)))
      !current_point_evaluation_values (hST.1 a b) (hUT.1 a b).
    have hSource:ea (c*:S+U) a=c*ea S a+ea U a.
      change (@current_point_evaluation R h2 m i A hA a (c*:S+U)=
        c*:@current_point_evaluation R h2 m i A hA a S+@current_point_evaluation R h2 m i A hA a U).
      exact:(hom_linear (@current_point_evaluation R h2 m i A hA a) c S U).
    rewrite hSource mulrDl.
    change (c*(ea S a*eb T b)+ea U a*eb T b=c*ea S a*eb T b+ea U a*eb T b).
    by rewrite mulrA.
  + move=>k l e hk a b.
    pose test:=@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b).
    change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB test
      (c*:Product S T+Product U T)=0).
    rewrite (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB test))
      !current_point_evaluation_values.
    by rewrite (hST.2 k l e hk a b) (hUT.2 k l e hk a b) scaler0 add0r.
Qed.

(** Source for [current_cartesian_product_second_linear]: the
    original Cartesian current product is linear in its
    second factor, Federer 4.1.8, p. 361. No
    measure-representation hypothesis is added. *)
Theorem current_cartesian_product_second_linear (S:CA) c (T U:CB):
  Product S (c*:T+U)=c*:Product S T+Product S U.
Proof.
apply:(@current_cartesian_product_unique R h2 m n i j A B hA hB S (c*:T+U)
  (Product S (c*:T+U)) (c*:Product S T+Product S U)).
- exact:(@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S (c*:T+U)).
- have hST:=@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T.
  have hSU:=@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S U.
  split.
  + move=>a b.
    change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB (Pure i j a b)
      (c*:Product S T+Product S U)=ea S a*eb (c*:T+U) b).
    rewrite (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB (Pure i j a b)))
      !current_point_evaluation_values (hST.1 a b) (hSU.1 a b).
    have hSource:eb (c*:T+U) b=c*eb T b+eb U b.
      change (@current_point_evaluation R h2 n j B hB b (c*:T+U)=
        c*:@current_point_evaluation R h2 n j B hB b T+@current_point_evaluation R h2 n j B hB b U).
      exact:(hom_linear (@current_point_evaluation R h2 n j B hB b) c T U).
    rewrite hSource mulrDr.
    change (c*(ea S a*eb T b)+ea S a*eb U b=ea S a*(c*eb T b)+ea S a*eb U b).
    by rewrite (mulrCA c (ea S a) (eb T b)).
  + move=>k l e hk a b.
    pose test:=@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b).
    change (@current_point_evaluation R h2 (m+n) (i+j) AB hAB test
      (c*:Product S T+Product S U)=0).
    rewrite (hom_linear (@current_point_evaluation R h2 (m+n) (i+j) AB hAB test))
      !current_point_evaluation_values.
    by rewrite (hST.2 k l e hk a b) (hSU.2 k l e hk a b) scaler0 add0r.
Qed.

(** Source for [current_cartesian_product_bilinear]: the
    Cartesian product of currents is a bilinear operation,
    Federer 4.1.8, p. 361, first sentence. *)
Theorem current_cartesian_product_bilinear:bilinear Product.
Proof.
split.
- move=>T c S U;exact:(current_cartesian_product_first_linear T c S U).
- move=>S c T U;exact:(current_cartesian_product_second_linear S c T U).
Qed.
End CurrentCartesianProductBilinear.

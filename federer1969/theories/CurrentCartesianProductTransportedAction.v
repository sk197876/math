(** Federer (1969), 4.1.8, p. 360: original mixed tests
    and equal-degree identifications for the product formulas.
    All current and test spaces are the actual opaque spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianProductTransportedAction.
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

(** Source for [current_cartesian_product_transported_diagonal]:
    the original diagonal separated-test equation survives
    every equal-degree identification, supporting the product
    boundary formulas in Federer 4.1.8, p. 360. *)
Theorem current_cartesian_product_transported_diagonal i j r
    (e:(i+j)%N=r) (f:(i+j)%N=r) (S:CA i) (T:CB j) (a:DA i) (b:DB j):
  ec r (CTr _ _ e (Product i j S T)) (Tr _ _ f (Pure i j a b))=
    ea i S a*eb j T b.
Proof.
change (@current_value R h2 (m+n) AB hAB r
  (CTr _ _ e (Product i j S T)) (Tr _ _ f (Pure i j a b))=ea i S a*eb j T b).
rewrite (@current_degree_transport_evaluation R h2 (m+n) AB hAB (i+j) r e
  (Product i j S T) (Tr _ _ f (Pure i j a b)))
  current_test_degree_transport_composition current_test_degree_transport_identity.
exact:((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).1 a b).
Qed.

(** Source for [current_cartesian_product_transported_off_diagonal]:
    the original off-diagonal equation survives equal-degree
    identifications for every mixed test degree, supporting
    Federer 4.1.8, p. 360. *)
Theorem current_cartesian_product_transported_off_diagonal i j r
    (e:(i+j)%N=r) (S:CA i) (T:CB j) k l
    (f:(k+l)%N=r) (hk:k<>i) (a:DA k) (b:DB l):
  ec r (CTr _ _ e (Product i j S T)) (Tr _ _ f (Pure k l a b))=0.
Proof.
change (@current_value R h2 (m+n) AB hAB r
  (CTr _ _ e (Product i j S T)) (Tr _ _ f (Pure k l a b))=0).
rewrite (@current_degree_transport_evaluation R h2 (m+n) AB hAB (i+j) r e
  (Product i j S T) (Tr _ _ f (Pure k l a b)))
  current_test_degree_transport_composition.
exact:((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).2
  k l (eq_trans f (esym e)) hk a b).
Qed.

(** Source for [current_cartesian_product_transported_off_second]:
    the off-diagonal separated-test equation also vanishes
    when the second test degree differs from the second
    current degree, supporting Federer 4.1.8, p. 360. *)
Theorem current_cartesian_product_transported_off_second i j r
    (e:(i+j)%N=r) (S:CA i) (T:CB j) k l
    (f:(k+l)%N=r) (hl:l<>j) (a:DA k) (b:DB l):
  ec r (CTr _ _ e (Product i j S T)) (Tr _ _ f (Pure k l a b))=0.
Proof.
have hk:k<>i.
  move=>hk;subst k.
  apply:hl;apply/eqP.
  have heq:(i+l == i+j)%N:=introT eqP (eq_trans f (esym e)).
  by rewrite eqn_add2l in heq.
exact:(@current_cartesian_product_transported_off_diagonal i j r e S T k l f hk a b).
Qed.
End CurrentCartesianProductTransportedAction.

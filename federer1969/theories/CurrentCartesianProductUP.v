(** Federer (1969), 4.1.8, p. 360: independent specification
    of the Cartesian product current by all separated test degrees.
    Equal-degree transports are the existing public identifications.
    The off-diagonal clause is retained for every valid mixed degree. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentDegreeTransport CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianProductUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).
Local Notation CA := (fun k=>@current_space R h2 m A hA k).
Local Notation CB := (fun k=>@current_space R h2 n B hB k).
Local Notation CC := (fun k=>@current_space R h2 (m+n) AB hAB k).
Local Notation ea := (fun k=>@current_value R h2 m A hA k).
Local Notation eb := (fun k=>@current_value R h2 n B hB k).
Local Notation ec := (fun k=>@current_value R h2 (m+n) AB hAB k).
Variable F:forall k l,DA k->DB l->DC (k+l).

(** Source for [is_current_cartesian_product]: the two displayed
    characterising equations for S times T in Federer 4.1.8, p. 360.
    The diagonal value is S(alpha)T(beta). Every off-diagonal mixed
    degree has value zero. This definition adds no existence,
    uniqueness, support or continuity assumption. *)
Definition is_current_cartesian_product i j (S:CA i) (T:CB j)
    (P:CC (i+j)):Prop:=
  (forall alpha beta,ec (i+j) P (@F i j alpha beta)=ea i S alpha*eb j T beta) /\
  (forall k l (e:(k+l)%N=(i+j)%N),k<>i->
    forall alpha beta,ec (i+j) P
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
        (@F k l alpha beta))=0).
End CurrentCartesianProductUP.

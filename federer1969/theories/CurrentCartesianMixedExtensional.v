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
Section CurrentCartesianMixedExtensional.
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

(** Source for [current_cartesian_mixed_values_extensional]:
    the complete mixed separated tests determine any original
    current on A times B, supporting the product identities
    of Federer 4.1.8, pp. 360–361, by the proved
    annihilator consequence of 4.1.3, p. 348. *)
Theorem current_cartesian_mixed_values_extensional d (P Q:CC d):
  (forall k l (e:(k+l)%N=d) (a:DA k) (b:DB l),
    ec d P (Tr _ _ e (Pure k l a b))=
      ec d Q (Tr _ _ e (Pure k l a b)))->P=Q.
Proof.
move=>hEqual.
have hZero:forall k l (e:(k+l)%N=d) (a:DA k) (b:DB l),
    ec d (P-Q) (Tr _ _ e (Pure k l a b))=0.
  move=>k l e a b.
  change (@current_point_evaluation R h2 (m+n) d AB hAB
    (Tr _ _ e (Pure k l a b)) (P-Q)=0).
  by rewrite (linB (hom_linear (@current_point_evaluation R h2 (m+n) d AB hAB
    (Tr _ _ e (Pure k l a b))))) !current_point_evaluation_values (hEqual k l e a b) subrr.
have hAll:=@current_cartesian_mixed_annihilator_zero R h2 m n d A B hA hB (P-Q) hZero.
apply:(@current_values_extensional R h2 (m+n) d AB hAB)=>phi.
have hValue:=hAll phi.
change (@current_point_evaluation R h2 (m+n) d AB hAB phi (P-Q)=0) in hValue.
rewrite (linB (hom_linear (@current_point_evaluation R h2 (m+n) d AB hAB phi)))
  !current_point_evaluation_values in hValue.
apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hValue.
Qed.
End CurrentCartesianMixedExtensional.

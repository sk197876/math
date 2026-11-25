(** Federer (1969), 4.1.11, p. 365: reuse the preceding
    Cartesian boundary rule with matching natural-degree indices.
    These transports identify equal degrees only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  CurrentCartesianProductTransportedAction CurrentCartesianMixedExtensional
  CurrentCartesianBoundaryTests CurrentBoundary CurrentTestExteriorDerivative CurrentBoundaryDegreeTransport CurrentCartesianBoundaryPositive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianBoundaryPositiveAligned.
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


(** Source for [current_cartesian_boundary_positive_aligned]:
    the original product boundary formula, with its output degree
    associated as the first degree plus the second lower degree.
    This supporting identification is used for S times ([0,1]
    times T) in Federer 4.1.11, p. 365. The theorem of 4.1.8,
    p. 360, is reused without a new proof of the product rule. *)
Theorem current_cartesian_boundary_positive_aligned i j (S:CA i.+1) (T:CB j.+1):
  bdC (i.+1+j) (CTr _ _ (addnS i.+1 j) (Product i.+1 j.+1 S T))=
    CTr _ _ (eq_trans (addnS i j) (esym (addSn i j)))
      (Product i j.+1 (bdA i S) T)+
    (-1:R)^+i.+1*:Product i.+1 j S (bdB j T).
Proof.
pose e:(i+j.+1)%N=(i.+1+j)%N:=eq_trans (addnS i j) (esym (addSn i j)).
have h:=congr1 (CTr _ _ e)
  (@current_cartesian_boundary_positive R h2 m n A B hA hB i j S T).
rewrite (linD (hom_linear (CTr _ _ e))) (linZ (hom_linear (CTr _ _ e)))
  current_degree_transport_roundtrip in h.
rewrite current_boundary_degree_transport current_degree_transport_composition in h.
have hProof:eq_trans (addSn i j.+1) (congr1 (fun r:nat=>r.+1) e)=addnS i.+1 j:=
  Prop_irrelevance _ _.
by rewrite hProof in h.
Qed.
End CurrentCartesianBoundaryPositiveAligned.

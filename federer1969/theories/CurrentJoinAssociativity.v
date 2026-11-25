(** Federer (1969), 4.1.11, p. 366: expand
    joins are associative. Identify the two original
    five-factor images by the printed barycentric
    triangle argument, then reuse their literal join
    expansions. No representation premise is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct
  CurrentAmbientProductImageEquation CurrentCartesianMapClass CurrentJoinSliceMapClass CurrentJoinDomain
  CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinLaws CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinAmbientSource CurrentJoinAmbientImage CurrentJoinAssociativityIteratedMaps
  CurrentJoinAssociativityLeftImage CurrentJoinAssociativityRightImage
  CurrentJoinAssociativityFiveEquality SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_associativity_degree]: the two
    original iterated joins have equal total degree,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_associativity_degree i j k:
  ((i+1+j)+1+k)%N=(i+1+(j+1+k))%N.
Proof. by rewrite !addnA. Qed.

Section CurrentJoinAssociativity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j k:nat.
Local Notation dj := ((n+(1+n))%N).
Local Notation df := ((n+(1+dj))%N).
Local Notation q := ((j+(1+k))%N).
Local Notation r := ((j+1+k)%N).
Local Notation d := ((i+(1+q))%N).
Local Notation Full := (fun a:nat=>fun _:R_n R a=>True).
Local Notation hFull := (fun (a:nat) (x:R_n R a) (_:True)=>
  @norm_full_domain_interior R (R_n R a) (inner_norm (@euclidean_inner_productP R a)) x).
Variables (P:@current_space R h2 n (Full n) (hFull n) i)
  (S:@current_space R h2 n (Full n) (hFull n) j)
  (T:@current_space R h2 n (Full n) (hFull n) k).
Hypothesis hP:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) i P).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) k T).
Local Notation PS := (@CurrentJoin.value R h2 n i j P S hP hS).
Local Notation hPS := (@current_join_compact R h2 n i j P S hP hS).
Local Notation ST := (@CurrentJoin.value R h2 n j k S T hS hT).
Local Notation hST := (@current_join_compact R h2 n j k S T hS hT).
Local Notation Left := (@CurrentJoin.value R h2 n (i+1+j)%N k PS T hPS hT).
Local Notation Right := (@CurrentJoin.value R h2 n i (j+1+k)%N P ST hP hST).

(** Source for [current_join_associativity]: the actual
    compact-current joins satisfy (R join S) join T =
    R join (S join T), Federer 4.1.11, p. 366.
    Only their equal natural degrees are identified.
    The original common-square and barycentric maps
    prove the assertion for arbitrary compact currents,
    including zero degrees and dimension zero. *)
Lemma current_join_associativity:
  @current_degree_transport R h2 n (Full n) (hFull n)
    ((i+1+j)+1+k)%N (i+1+(j+1+k))%N (current_join_associativity_degree i j k) Left=Right.
Proof.
rewrite (@current_join_assoc_left_image R h2 n i j k P S T hP hS hT)
  current_degree_transport_composition.
have hDegree:(eq_trans (current_join_assoc_left_degree i j k)
    (current_join_associativity_degree i j k))=current_join_assoc_right_degree i j k:=Prop_irrelevance _ _.
rewrite hDegree (@current_join_assoc_five_factor_equality R h2 n i j k P S T hP hS hT).
exact:esym (@current_join_assoc_right_image R h2 n i j k P S T hP hS hT).
Qed.
End CurrentJoinAssociativity.

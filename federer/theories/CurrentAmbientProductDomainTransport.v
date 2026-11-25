(** Federer (1969), 4.1.11, p. 366: equal
    whole-space presentations of the original Cartesian
    factors give the same actual product. This adapter
    serves the finite rectangle and iterated join
    identities without constructing a new product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentDomainTransport
  CurrentAmbientCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductDomainTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall y,B y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B y.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Hypothesis eA:A=Full m.
Hypothesis eB:B=Full n.
Hypothesis eAB:AB=Full (m+n)%N.

(** Source for [current_ambient_product_domain_transport]:
    equality transport of the original product is the
    ambient product of the equality-transported factors,
    supporting the rectangular and iterated join identities
    in Federer 4.1.11, p. 366. Only equal domains
    and their openness proofs are identified. *)
Theorem current_ambient_product_domain_transport i j
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  @current_domain_transport R h2 (m+n)%N AB hAB (Full (m+n)%N) eAB (hFull (m+n)%N) (i+j)%N
    (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T)=
  @current_ambient_cartesian_product R h2 m n i j
    (@current_domain_transport R h2 m A hA (Full m) eA (hFull m) i S)
    (@current_domain_transport R h2 n B hB (Full n) eB (hFull n) j T).
Proof.
subst A;subst B.
have hFirst:hA=hFull m:=Prop_irrelevance _ _;subst hA.
have hSecond:hB=hFull n:=Prop_irrelevance _ _;subst hB.
have hEquality:eAB=@current_cartesian_full_domain R m n:=Prop_irrelevance _ _.
by rewrite hEquality !current_domain_transport_refl.
Qed.
End CurrentAmbientProductDomainTransport.

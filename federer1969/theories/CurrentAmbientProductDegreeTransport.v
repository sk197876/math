(** Federer (1969), 4.1.11, p. 366: the
    original full-space Cartesian product respects equal
    natural degrees. Equality elimination changes no
    current or ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentAmbientCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductDegreeTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).

(** Source for [current_ambient_product_degree_transport]: the
    original product identifies equal degrees in both
    factors and their sum, supporting the time-factor
    reorderings in Federer 4.1.11, p. 366. *)
Lemma current_ambient_product_degree_transport i j i' j' (ei:i = i') (ej:j = j')
    (S:@current_space R h2 m (Full m) (hFull m) i)
    (T:@current_space R h2 n (Full n) (hFull n) j):
  @current_degree_transport R h2 (m+n)%N (Full (m+n)%N) (hFull (m+n)%N)
    (i+j)%N (i'+j')%N (congr2 addn ei ej)
    (@current_ambient_cartesian_product R h2 m n i j S T)=
  @current_ambient_cartesian_product R h2 m n i' j'
    (@current_degree_transport R h2 m (Full m) (hFull m) i i' ei S)
    (@current_degree_transport R h2 n (Full n) (hFull n) j j' ej T).
Proof.
case:i' /ei;case:j' /ej.
by rewrite !current_degree_transport_identity.
Qed.
End CurrentAmbientProductDegreeTransport.

(** Federer (1969), 4.1.11, p. 366: equality
    of the original containing domains commutes with
    equality of natural current degrees. Both adapters
    identify only equal data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDomainTransport CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_domain_transport_degree]: equal
    domain and degree identifications commute, supporting
    the original prism boundary in Federer 4.1.11,
    p. 366. No degree or domain hypothesis is strengthened. *)
Theorem current_domain_transport_degree (R:realType) (h2:(1+1:R)!=0) n
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (e:U=V)
    (hV:forall x,V x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V x)
    i j (d:i=j) (T:@current_space R h2 n U hU i):
  @current_domain_transport R h2 n U hU V e hV j
    (@current_degree_transport R h2 n U hU i j d T)=
  @current_degree_transport R h2 n V hV i j d
    (@current_domain_transport R h2 n U hU V e hV i T).
Proof.
subst V.
have hOpen:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite !current_domain_transport_refl.
Qed.

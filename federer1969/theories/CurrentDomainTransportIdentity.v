(** Federer (1969), 4.1.11, p. 366: an
    equality-only identification of the same original
    containing domain fixes its current. This supports
    the empty and singleton rectangular products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDomainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_domain_transport_identity]: every
    self-equality proof of the original domain gives
    the identity current map, supporting the rectangular
    decomposition in Federer 4.1.11, p. 366. *)
Theorem current_domain_transport_identity (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (e:U=U) k (T:@current_space R h2 n U hU k):
  @current_domain_transport R h2 n U hU U e hU k T=T.
Proof.
have hEquality:e=erefl U:=Prop_irrelevance _ _.
by rewrite hEquality current_domain_transport_refl.
Qed.

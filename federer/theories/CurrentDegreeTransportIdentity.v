(** Federer (1969), 4.1.7, p. 356: equal
    original degrees are identified without changing
    a current or test. Proof irrelevance
    removes only equality-proof bookkeeping. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportIdentity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.

(** Source for [current_degree_transport_identity]:
    an equality of a degree with itself
    acts identically on actual currents,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_degree_transport_identity m (h:m=m) (T:@current_space R h2 n U hU m):
  @current_degree_transport R h2 n U hU m m h T=T.
Proof.
have hEq:h=erefl m:=Prop_irrelevance _ _.
by rewrite hEq.
Qed.

(** Source for [current_degree_transport_roundtrip]:
    identifying two equal dimensions and then
    returning preserves the actual current,
    supporting Federer 4.1.7, p. 356.
    Equality proofs carry no mathematical data. *)
Lemma current_degree_transport_roundtrip m q (h:m=q) (k:q=m)
    (T:@current_space R h2 n U hU m):
  @current_degree_transport R h2 n U hU q m k
    (@current_degree_transport R h2 n U hU m q h T)=T.
Proof.
case:q /h in k *.
by rewrite !current_degree_transport_identity.
Qed.

(** Source for [current_test_degree_transport_identity]:
    an equal-degree identification acts identically
    on actual compact tests, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_test_degree_transport_identity m (h:m=m) (phi:@current_test_space R h2 n U hU m):
  @current_test_degree_transport R h2 n U hU m m h phi=phi.
Proof.
have hEq:h=erefl m:=Prop_irrelevance _ _.
by rewrite hEq.
Qed.
End CurrentDegreeTransportIdentity.

(** Federer (1969), 4.1.7, p. 358, used in
    4.1.12, p. 369: identification of equal natural
    current degrees preserves local normality and
    normality. These are the existing degree maps;
    only their equality bookkeeping is involved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport
  CurrentDegreeTransportIdentity NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section NormalCurrentDegreeTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.

(** Source for [locally_normal_current_degree_transport]:
    equal-degree identification preserves local normality,
    supporting the zero and positive boundary cases
    in Federer 4.1.12, p. 369, by the
    original definition in 4.1.7, p. 358. *)
Theorem locally_normal_current_degree_transport a b (e:a=b)
    (T:@current_space R h2 n U hU a):
  @is_locally_normal_current R h2 n U hU a T <->
  @is_locally_normal_current R h2 n U hU b
    (@current_degree_transport R h2 n U hU a b e T).
Proof. case:b /e;by rewrite current_degree_transport_identity. Qed.

(** Source for [normal_current_degree_transport]:
    equal-degree identification preserves normality,
    supporting Federer 4.1.12, p. 369,
    by the original compact-support definition in
    4.1.7, p. 358. *)
Theorem normal_current_degree_transport a b (e:a=b)
    (T:@current_space R h2 n U hU a):
  @is_normal_current R h2 n U hU a T <->
  @is_normal_current R h2 n U hU b
    (@current_degree_transport R h2 n U hU a b e T).
Proof. case:b /e;by rewrite current_degree_transport_identity. Qed.
End NormalCurrentDegreeTransport.

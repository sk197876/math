(** Federer (1969), 3.2.28(2),(3), pp. 265–266:
    exact natural dimensions of the coarea fibres. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanSkewIndexCardinality EuclideanStiefelTangentIndexDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_stiefel_dimension_split]: the
    Stiefel dimension is the Grassmann dimension plus
    the SO(m) dimension in Federer 3.2.28(2),
    p. 265. The identity includes m=0. *)
Lemma euclidean_stiefel_dimension_split m n:
  m<=n ->m*(2*n-m-1)%/2=m*(n-m)+m*(m-1)%/2.
Proof.
move=>hmn; have h:=euclidean_stiefel_tangent_index_cardinality hmn.
rewrite /euclidean_stiefel_tangent_indices card_sum card_prod !card_ord
  euclidean_skew_index_cardinality in h.
by rewrite -h addnC.
Qed.

(** Source for [euclidean_exterior_fibre_dimension]: the
    degree of the SO(m) fibre measure in Federer
    3.2.28(2), p. 265. Natural subtraction
    agrees with the printed dimension difference. *)
Lemma euclidean_exterior_fibre_dimension m n:
  m<=n ->m*(2*n-m-1)%/2-m*(n-m)=m*(m-1)%/2.
Proof. by move=>hmn; rewrite (euclidean_stiefel_dimension_split hmn) addKn. Qed.

(** Source for [euclidean_skew_dimension_successor]: the
    m-1 extra skew directions for the forgetful map,
    Federer 3.2.28(3), pp. 265–266. *)
Lemma euclidean_skew_dimension_successor k:
  k.+1*(k.+1-1)%/2=k*(k-1)%/2+k.
Proof.
have hPoly:k.+1*(k.+1-1)=k*(k-1)+k*2.
  case:k=>[|k]; first by rewrite !mul0n.
  rewrite !subn1 !succnK [k.+2*k.+1]mulnC -mulnDr.
  by rewrite addn2.
by rewrite hPoly divnDMl.
Qed.

(** Source for [euclidean_forgetful_dimension_split]:
    the source dimension equals the target dimension
    plus n-m in Federer 3.2.28(3), p. 266,
    with m=k+1 and k+1<=n. *)
Lemma euclidean_forgetful_dimension_split k n:
  k.+1<=n ->k.+1*(2*n-k.+1-1)%/2=k*(2*n-k-1)%/2+(n-k-1).
Proof.
move=>hkn.
have hk: k<=n:=leq_trans (leqnSn k) hkn.
have hPos:0<n-k by rewrite subn_gt0.
have hN:n-k=(n-k-1).+1 by rewrite subn1 prednK.
have hS:n-k.+1=n-k-1 by rewrite subnS subn1.
rewrite !euclidean_stiefel_dimension_split // euclidean_skew_dimension_successor hS hN mulSn mulnS.
rewrite !subn1 !succnK !addnA.
rewrite [((n-k).-1)+k*((n-k).-1)]addnC
  [k*((n-k).-1)+((n-k).-1)+k*k.-1%/2]addnAC
  [k*((n-k).-1)+k*k.-1%/2+((n-k).-1)+k]addnAC
  [k*((n-k).-1)+k*k.-1%/2+k]addnC.
by rewrite addnA.
Qed.

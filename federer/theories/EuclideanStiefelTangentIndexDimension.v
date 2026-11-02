(** Federer (1969), 3.2.28(3), p. 265:
    count the skew and normal tangent basis directions
    and compare with the Stiefel dimension in part (1). *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanSkewIndexCardinality EuclideanStiefelDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_stiefel_tangent_indices]: one
    index per displayed a_ij or b_ij in Federer
    3.2.28(3), p. 265. The normal target
    indices have cardinality n-m. *)
Definition euclidean_stiefel_tangent_indices m n:finType:=
  Finite.clone ((euclidean_skew_indices m)+('I_m*'I_(n-m)))%type _.

(** Source for [euclidean_symmetric_skew_dimension_sum]:
    the symmetric and skew entry counts sum to m^2,
    supporting the tangent basis count in Federer
    3.2.28(1),(3), pp. 263,265, by 1.6.1,
    p. 23. Natural degree zero is included. *)
Lemma euclidean_symmetric_skew_dimension_sum m:
  m*(m+1)%/2+m*(m-1)%/2=m * m.
Proof.
have hSmall:m<=m * m.
  case:m=>[|m]; first exact:leqnn.
  exact:(@leq_pmulr m.+1 m.+1 (ltn0Sn m)).
have hEven:2%|m*(m+1) by rewrite dvdn2 oddM addn1 oddS andbN.
have hAdj:m*(m+1)+m*(m-1)=(m * m)*2.
  rewrite addn1 mulnS mulnBr muln1 [m+m * m]addnC -addnA.
  by rewrite addnBA // addKn addnn -muln2.
by rewrite -(@divnDl (m*(m+1)) (m*(m-1)) 2 hEven) hAdj mulnK.
Qed.

(** Source for [euclidean_stiefel_tangent_index_cardinality]:
    the displayed a_ij and b_ij families together
    have exactly m(2n-m-1)/2 members, Federer
    3.2.28(3), p. 265. The ambient dimension
    bound is precisely the printed m<=n. *)
Theorem euclidean_stiefel_tangent_index_cardinality m n:
  m<=n ->#|{:euclidean_stiefel_tangent_indices m n}|=m*(2*n-m-1)%/2.
Proof.
move=>hmn.
have hBound:m * m<=m*n:=leq_mul (leqnn m) hmn.
have hSum:=euclidean_symmetric_skew_dimension_sum m.
have hSkew:m*(m-1)%/2<=m * m by rewrite -hSum leq_addl.
have hSym:m*(m+1)%/2=m * m-m*(m-1)%/2 by rewrite -hSum addnK.
rewrite /euclidean_stiefel_tangent_indices card_sum card_prod !card_ord
  euclidean_skew_index_cardinality euclidean_stiefel_dimension_identity hSym.
rewrite (subnA hSkew hBound) !mulnBr addnC; reflexivity.
Qed.

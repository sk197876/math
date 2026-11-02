(** Federer (1969), 3.2.28(3), p. 266:
    exactly k=m-1 of the nonzero differential
    coefficients equal 2^(-1/2); every other
    coefficient equals one. Compute their product. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EuclideanSkewIndexCardinality EuclideanStiefelHalfNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_forgetful_tangent_coefficient]:
    the nonzero coefficient attached to each target
    c_ij,d_ij direction in Federer 3.2.28(3),
    p. 266. The final normal index is g(e_m). *)
Definition euclidean_forgetful_tangent_coefficient (R:realType) k r (c:R)
    (j:((euclidean_skew_indices k)+('I_k*'I_r.+1))%type):R:=
  match j with
  | inl _=>1
  | inr p=>if p.2==ord_max then c else 1
  end.

(** Source for [euclidean_forgetful_tangent_coefficient_nonnegative]:
    nonnegative singular lengths in the Jacobian calculation,
    Federer 3.2.28(3), p. 266. *)
Lemma euclidean_forgetful_tangent_coefficient_nonnegative (R:realType) k r (c:R):
  0<=c ->forall j,@euclidean_forgetful_tangent_coefficient R k r c j>=0.
Proof. move=>hc [q|[i l]] /=; first exact:ler01; by case:(l==ord_max). Qed.

(** Source for [euclidean_forgetful_tangent_coefficient_product]:
    the product of the nonzero displayed DS coefficients
    is c^k, Federer 3.2.28(3), p. 266.
    This counts coefficients without a dimension or
    normalization premise on a geometric map. *)
Theorem euclidean_forgetful_tangent_coefficient_product (R:realType) k r (c:R):
  \prod_j (@euclidean_forgetful_tangent_coefficient R k r c j)=c^+k.
Proof.
rewrite big_sumType /euclidean_forgetful_tangent_coefficient /=.
have hSkew:(\prod_(p:euclidean_skew_indices k) (1:R))= 1 by apply:big1.
rewrite hSkew mul1r.
change ((\prod_(p:('I_k*'I_r.+1)%type) (if p.2==ord_max then c else 1))=c^+k).
rewrite -(pair_bigA _ (fun (_:'I_k) (j:'I_r.+1)=>(if j==ord_max then c else 1:R))).
have hInner:(\prod_(j:'I_r.+1) (if j==ord_max then c else 1))=c.
  rewrite (bigD1 ord_max) //= eqxx.
  have hRest:(\prod_(j:'I_r.+1|j!=ord_max) (if j==ord_max then c else 1))= 1.
    by apply:big1=>j hj; rewrite (negbTE hj).
  by rewrite hRest mulr1.
under eq_bigr do rewrite hInner.
by rewrite prodr_const card_ord.
Qed.

(** Source for [euclidean_forgetful_half_coefficient_product]:
    the actual displayed Jacobian factor is
    (1/sqrt(2))^(m-1), Federer 3.2.28(3),
    p. 266, including k=0. *)
Theorem euclidean_forgetful_half_coefficient_product (R:realType) k r:
  \prod_j (@euclidean_forgetful_tangent_coefficient R k r (Num.sqrt (2:R))^-1 j)=
    (Num.sqrt (2:R))^-k.
Proof. by rewrite euclidean_forgetful_tangent_coefficient_product exprVn. Qed.

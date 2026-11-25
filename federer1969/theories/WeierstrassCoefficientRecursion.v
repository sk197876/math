(** Federer (1969), 3.4.6, p. 324: the original
    quotient coefficient recursion exists and is unique by
    its strictly decreasing natural weight. These are actual
    functions, before homogeneity or convergence is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals functions.
From Federer Require Import RankedDoubleRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Recursion.
Variable R:realType.
Variable K:Type.

(** Source for [weierstrass_coefficient_weight]: the original
    weight i+(k+1)j used for the quotient recursion in
    3.4.6, p. 324. *)
Definition weierstrass_coefficient_weight k i j:nat:=(i+k.+1*j)%N.

(** Source for [weierstrass_prefix_weight_smaller]: each
    original same-transverse-degree predecessor has smaller
    weight, supporting 3.4.6, p. 324. *)
Lemma weierstrass_prefix_weight_smaller k i j mu:
  (mu<i)%N ->(weierstrass_coefficient_weight k mu j<weierstrass_coefficient_weight k i j)%N.
Proof. by rewrite /weierstrass_coefficient_weight ltn_add2r. Qed.

(** Source for [weierstrass_cross_weight_smaller]: every
    original cross-degree predecessor mu<=i+k, nu<j has
    smaller weight, supporting 3.4.6, p. 324. *)
Lemma weierstrass_cross_weight_smaller k i j mu nu:
  (mu<=i+k)%N ->(nu<j)%N ->
  (weierstrass_coefficient_weight k mu nu<weierstrass_coefficient_weight k i j)%N.
Proof.
move=>hMu hNu.
have hFirst:(mu+k.+1*nu<=i+k+k.+1*nu)%N by rewrite leq_add2r.
have hSecond:(i+k+k.+1*nu<i+k.+1+k.+1*nu)%N by rewrite ltn_add2r ltn_add2l.
have hThird:(i+k.+1+k.+1*nu<=i+k.+1*j)%N.
  rewrite -addnA -mulnS leq_add2l.
  exact:(leq_mul (leqnn k.+1) hNu).
exact:(leq_ltn_trans hFirst (leq_trans hSecond hThird)).
Qed.

(** Source for [weierstrass_coefficient_step]: the exact
    three-term recurrence for Q_(i,j) on 3.4.6, p. 324.
    Both finite upper index bounds and the original
    truncated natural differences are retained. *)
Definition weierstrass_coefficient_step k (phi psi:nat->nat->K->R)
    i j (q:nat->nat->K->R) (z:K):R:=
  psi (i+k)%N j z-
    \sum_(mu<i) q mu j z*phi (i+k-mu)%N 0%N z-
    \sum_(mu<(i+k).+1) \sum_(nu<j) q mu nu z*phi (i+k-mu)%N (j-nu)%N z.

(** Source for [weierstrass_coefficient_step_local]: the
    printed recurrence uses only strictly smaller weights,
    proving the induction claim in 3.4.6, p. 324. *)
Lemma weierstrass_coefficient_step_local k (phi psi:nat->nat->K->R) i j
    (f g:nat->nat->K->R):
  (forall p q,(weierstrass_coefficient_weight k p q<weierstrass_coefficient_weight k i j)%N ->
    f p q=g p q) ->
  weierstrass_coefficient_step k phi psi i j f=weierstrass_coefficient_step k phi psi i j g.
Proof.
move=>hAgree;apply:funext=>z.
have hPrefix:(\sum_(mu<i) f mu j z*phi (i+k-mu)%N 0%N z)=
    \sum_(mu<i) g mu j z*phi (i+k-mu)%N 0%N z.
  apply:eq_bigr=>mu _.
  by rewrite (hAgree mu j (@weierstrass_prefix_weight_smaller k i j mu (ltn_ord mu))).
have hCross:(\sum_(mu<(i+k).+1) \sum_(nu<j) f mu nu z*phi (i+k-mu)%N (j-nu)%N z)=
    \sum_(mu<(i+k).+1) \sum_(nu<j) g mu nu z*phi (i+k-mu)%N (j-nu)%N z.
  apply:eq_bigr=>mu _;apply:eq_bigr=>nu _.
  have hMu:(mu<=i+k)%N by have:=ltn_ord mu;rewrite ltnS.
  by rewrite (hAgree mu nu (@weierstrass_cross_weight_smaller k i j mu nu hMu (ltn_ord nu))).
by rewrite /weierstrass_coefficient_step hPrefix hCross.
Qed.

(** Source for [weierstrass_coefficient_recursion_exists]: the
    actual original coefficient functions Q_(i,j) exist for
    all nonnegative i,j, as claimed in 3.4.6, p. 324.
    Their later bounds and analytic realisation remain separate. *)
Theorem weierstrass_coefficient_recursion_exists k (phi psi:nat->nat->K->R):
  exists q:nat->nat->K->R,forall i j,
    q i j=weierstrass_coefficient_step k phi psi i j q.
Proof.
have hExists:=(@ranked_double_recursion_exists (fun _=>[the zmodType of (K->R^o)])
  (weierstrass_coefficient_weight k) (weierstrass_coefficient_step k phi psi)
  (@weierstrass_coefficient_step_local k phi psi)).
exact:hExists.
Qed.

(** Source for [weierstrass_coefficient_recursion_unique]: the
    original equations determine every quotient coefficient
    uniquely, supporting the germ uniqueness assertion of
    3.4.6, p. 324. No convergence is assumed. *)
Theorem weierstrass_coefficient_recursion_unique k (phi psi f g:nat->nat->K->R):
  (forall i j,f i j=weierstrass_coefficient_step k phi psi i j f) ->
  (forall i j,g i j=weierstrass_coefficient_step k phi psi i j g) ->
  forall i j,f i j=g i j.
Proof.
exact:(@ranked_double_recursion_unique (fun _=>[the zmodType of (K->R^o)])
  (weierstrass_coefficient_weight k) (weierstrass_coefficient_step k phi psi)
  (@weierstrass_coefficient_step_local k phi psi) f g).
Qed.
End Recursion.

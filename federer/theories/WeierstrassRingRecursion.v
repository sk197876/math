(** Federer (1969), 3.4.12, p. 339:
    the coefficient recurrence of 3.4.6, p. 324,
    uses ring arithmetic independently of its real bounds.
    This connection reuses the original decreasing weight
    and the proved ranked double recursion for complex coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import RankedDoubleRecursion WeierstrassCoefficientRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Recursion.
Variable F:comNzRingType.
Variable K:Type.

(** Source for [weierstrass_ring_coefficient_step]: the
    literal original recurrence with coefficient ring separated
    from the real field of estimates, 3.4.6,
    p. 324, as required by 3.4.12, p. 339. *)
Definition weierstrass_ring_coefficient_step k (phi psi:nat->nat->K->F)
    i j (q:nat->nat->K->F) (z:K):F:=
  psi (i+k)%N j z-
    \sum_(mu<i) q mu j z*phi (i+k-mu)%N 0%N z-
    \sum_(mu<(i+k).+1) \sum_(nu<j) q mu nu z*phi (i+k-mu)%N (j-nu)%N z.

(** Source for [weierstrass_ring_coefficient_step_local]: the
    existing strictly smaller-weight dependencies remain valid
    for complex ring coefficients, 3.4.12, p. 339. *)
Lemma weierstrass_ring_coefficient_step_local k (phi psi:nat->nat->K->F) i j
    (f g:nat->nat->K->F):
  (forall p q,(weierstrass_coefficient_weight k p q<weierstrass_coefficient_weight k i j)%N ->
    f p q=g p q) ->
  weierstrass_ring_coefficient_step k phi psi i j f=
    weierstrass_ring_coefficient_step k phi psi i j g.
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
by rewrite /weierstrass_ring_coefficient_step hPrefix hCross.
Qed.

(** Source for [weierstrass_ring_coefficient_recursion_exists]: the
    original quotient recurrence has actual ring-valued coefficients,
    3.4.12, p. 339. Reuse ranked recursion;
    analytic realization is a separate obligation. *)
Theorem weierstrass_ring_coefficient_recursion_exists k (phi psi:nat->nat->K->F):
  exists q:nat->nat->K->F,forall i j,
    q i j=weierstrass_ring_coefficient_step k phi psi i j q.
Proof.
exact:(@ranked_double_recursion_exists (fun _=>[the zmodType of (K->F^o)])
  (weierstrass_coefficient_weight k) (weierstrass_ring_coefficient_step k phi psi)
  (@weierstrass_ring_coefficient_step_local k phi psi)).
Qed.

(** Source for [weierstrass_ring_coefficient_recursion_unique]: the
    exact original recurrence determines its ring-valued coefficients
    uniquely, 3.4.12, p. 339. No analytic
    quotient or convergence assertion is assumed. *)
Theorem weierstrass_ring_coefficient_recursion_unique k (phi psi f g:nat->nat->K->F):
  (forall i j,f i j=weierstrass_ring_coefficient_step k phi psi i j f) ->
  (forall i j,g i j=weierstrass_ring_coefficient_step k phi psi i j g) ->
  forall i j,f i j=g i j.
Proof.
exact:(@ranked_double_recursion_unique (fun _=>[the zmodType of (K->F^o)])
  (weierstrass_coefficient_weight k) (weierstrass_ring_coefficient_step k phi psi)
  (@weierstrass_ring_coefficient_step_local k phi psi) f g).
Qed.
End Recursion.

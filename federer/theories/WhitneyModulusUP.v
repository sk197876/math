(** Federer (1969), 3.1.14, p. 225:
    the modulus rho(C,delta) of a family of polynomial jets
    on a closed subset of R^m, specified as the sealed supremum
    of the printed quotients, and the hypothesis of Whitney's
    extension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP BoundedHom SymmetricForms SymmetricFormSum
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  SymmetricOperatorNormUP SymmetricOperatorNorm ExtendedSupremumUP ExtendedSupremumSealed
  ContinuousSymmetricFormAdapter FiniteInnerSymmetricFormBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WhitneyModulus.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable k : nat.
Variable P : X->PolynomialFunction (R_n R m) Y.

(** Source for [whitney_difference_norm]:
    the norm ||D^i P_a(b)-D^i P_b(b)|| in the
    definition of rho(C,delta), Federer 3.1.14,
    p. 225, where the ith differential of a polynomial
    is its ith Taylor coefficient form. *)
Definition whitney_difference_norm i (a b : X) : \bar R :=
  symmetric_operator_norm hN.1 NY
    (polynomial_taylor_coefficient (P a) i b-polynomial_taylor_coefficient (P b) i b).

(** Source for [whitney_difference_norm_finite]:
    every symmetric form on R^m is bounded, so the
    norms entering rho(C,delta) are finite, Federer
    3.1.14, p. 225, with 1.10.5. *)
Lemma whitney_difference_norm_finite i a b :
  exists q : R, whitney_difference_norm i a b=q%:E.
Proof.
have [C [hC hb]] := @finite_inner_symmetric_form_bounded R (R_n R m) Y _
  (@euclidean_inner_productP R m) NY hNY.1 m _ (@coordinate_basisP R m) i
  (polynomial_taylor_coefficient (P a) i b-polynomial_taylor_coefficient (P b) i b).
have hle : (whitney_difference_norm i a b<=C%:E)%E.
  apply/symmetric_operator_norm_bound=>t ht.
  apply: (le_trans (hb t)); rewrite -[C in X in _<=X]mulr1.
  apply: (ler_wpM2l hC); apply: prodr_ile1=>j _.
  by rewrite (real_seminorm_nonnegative hN.1) (ht j).
have hge : (0<=whitney_difference_norm i a b)%E.
  exact: (symmetric_operator_norm_ge_zero hN.1 hNY.1 _).
exists (fine (whitney_difference_norm i a b)); rewrite fineK //.
apply: fin_real; apply/andP; split.
- exact: (lt_le_trans (ltNyr 0) hge).
- exact: (le_lt_trans hle (ltry C)).
Qed.

(** Source for [whitney_quotient_set]:
    "the set of all numbers
    ||D^i P_a(b)-D^i P_b(b)|| |a-b|^(i-k) (k-i)!
    corresponding to i=0,...,k and a,b in C with
    0<|a-b|<=delta", Federer 3.1.14, p. 225. *)
Definition whitney_quotient_set (C : set X) (delta : R) : set R :=
  [set r | exists i (a b : X) (q : R), (i<=k)%N /\ C a /\ C b /\
    0<N (a-b) /\ N (a-b)<=delta /\ whitney_difference_norm i a b=q%:E /\
    r=q*(N (a-b))^-(k-i)%N*(((k-i)%N)`!)%:R].

(** Source for [whitney_quotient_set_nonempty]:
    the number zero is adjoined so that the supremum
    defining rho(C,delta) exists also for an empty set
    of quotients, Federer 3.1.14, p. 225. *)
Lemma whitney_quotient_set_nonempty (C : set X) (delta : R) :
  (whitney_quotient_set C delta `|` [set 0]) !=set0.
Proof. by exists 0; right. Qed.

(** Source for [whitney_modulus]:
    rho(C,delta), the supremum of the printed set of
    quotients, Federer 3.1.14, p. 225, with zero
    adjoined; it is a sealed extended real. *)
Definition whitney_modulus (C : set X) (delta : R) : \bar R :=
  ExtendedSupremum.value (whitney_quotient_set_nonempty C delta).

(** Source for [whitney_modulusP]:
    the supremum laws of rho(C,delta), Federer 3.1.14, p. 225. *)
Lemma whitney_modulusP (C : set X) (delta : R) :
  is_extended_supremum (whitney_quotient_set C delta `|` [set 0]) (whitney_modulus C delta).
Proof. exact: ExtendedSupremum.laws. Qed.

(** Source for [whitney_modulus_nonnegative]:
    rho(C,delta)>=0, since zero is adjoined,
    Federer 3.1.14, p. 225. *)
Lemma whitney_modulus_nonnegative (C : set X) (delta : R) :
  (0<=whitney_modulus C delta)%E.
Proof.
apply: (extended_supremum_upper (whitney_modulusP C delta)); by right.
Qed.

(** Source for [whitney_modulus_monotone]:
    rho(C,delta) is nondecreasing in delta and in C,
    supporting the limit hypothesis of Federer 3.1.14, p. 225. *)
Lemma whitney_modulus_monotone (C D : set X) (delta eta : R) :
  C `<=` D -> delta<=eta -> (whitney_modulus C delta<=whitney_modulus D eta)%E.
Proof.
move=>hCD hde; apply: (extended_supremum_least (whitney_modulusP C delta)).
move=>r [[i [a [b [q [hi [ha [hb [hp [hd [hq hr]]]]]]]]]]|->].
- apply: (extended_supremum_upper (whitney_modulusP D eta)); left.
  exists i, a, b, q; split=> //; split; first exact: hCD.
  split; first exact: hCD; split=> //; split=> //; exact: (le_trans hd hde).
- exact: whitney_modulus_nonnegative.
Qed.

(** Source for [whitney_modulus_bound]:
    an upper bound rho for rho(C,delta) gives
    ||D^i P_a(b)-D^i P_b(b)||<=rho |a-b|^(k-i)/(k-i)!
    for a,b in C with 0<|a-b|<=delta and i<=k,
    Federer 3.1.14, p. 225. *)
Theorem whitney_modulus_bound (C : set X) (delta rho : R) i (a b : X) :
  (whitney_modulus C delta<=rho%:E)%E -> (i<=k)%N -> C a -> C b ->
  0<N (a-b) -> N (a-b)<=delta ->
  (whitney_difference_norm i a b<=(rho*(N (a-b))^+(k-i)%N/(((k-i)%N)`!)%:R)%:E)%E.
Proof.
move=>hrho hi ha hb hp hd.
have [q hq] := whitney_difference_norm_finite i a b.
have hin : (whitney_quotient_set C delta `|` [set 0])
    (q*(N (a-b))^-(k-i)%N*(((k-i)%N)`!)%:R).
  by left; exists i, a, b, q.
have hle := le_trans (extended_supremum_upper (whitney_modulusP C delta) hin) hrho.
rewrite lee_fin mulrAC in hle.
have hpow : 0<(N (a-b))^+(k-i)%N := exprn_gt0 _ hp.
have hfact : 0<(((k-i)%N)`!)%:R :> R by rewrite ltr0n fact_gt0.
rewrite ler_pdivrMr // in hle.
by rewrite hq lee_fin ler_pdivlMr.
Qed.

(** Source for [is_whitney_jet_family]:
    the hypotheses of Whitney's extension theorem,
    Federer 3.1.14, p. 225: A is closed, each P_a has
    degree at most k, and rho(C,delta)->0 as delta->0+
    for each compact subset C of A. *)
Definition is_whitney_jet_family (A : set X) : Prop :=
  closed A /\
  (forall a, A a -> (polynomial_degree (P a)<=k)%N) /\
  forall C, C `<=` A -> compact C -> forall e : R, 0<e ->
    exists delta : R, 0<delta /\
      forall d, 0<d -> d<=delta -> (whitney_modulus C d<=e%:E)%E.
End WhitneyModulus.

(** Federer (1969), 3.1.13, p. 225:
    the sufficient constants V_i are nonnegative
    and depend only on C and G_0,...,G_i.
    Here C is the overlap bound 129^m. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import PartitionDerivativeBoundsUP PartitionDerivativeBoundsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partition_derivative_bounds_nonnegative]:
    the derivative constants can be chosen
    nonnegative, supporting the estimates of
    Federer 3.1.13, p. 225. *)
Lemma partition_derivative_bounds_nonnegative (R : realType)
    C (G V : nat->R) :
  0<=C -> (forall i, 0<=G i) -> is_partition_derivative_bounds C G V ->
  forall i, 0<=V i.
Proof.
move=>hC hG hV; elim/ltn_ind=>i ih.
case:i ih=>[|n] ih; first by rewrite hV.1.
rewrite hV.2; apply: addr_ge0; first exact: hG.
apply: (mulr_ge0 hC); apply: sumr_ge0=>j _.
apply: mulr_ge0; first exact: ler0n.
apply: mulr_ge0; first exact: hG.
exact: (ih j (ltn_ord j)).
Qed.

(** Source for [partition_derivative_bounds_initial_dependence]:
    V_i uses only G_0,...,G_i,
    as required in Federer 3.1.13,
    p. 225. Equality of later
    cutoff bounds is unnecessary. *)
Lemma partition_derivative_bounds_initial_dependence (R : realType)
    C (G H V W : nat->R) n :
  is_partition_derivative_bounds C G V ->
  is_partition_derivative_bounds C H W ->
  (forall i, (i<=n)%N -> G i=H i) ->
  forall i, (i<=n)%N -> V i=W i.
Proof.
move=>hV hW hGH.
elim/ltn_ind=>i ih hi.
case:i ih hi=>[|j] ih hj; first by rewrite hV.1 hW.1.
rewrite hV.2 hW.2 (hGH _ hj).
congr (H j.+1+C*_); apply: eq_bigr=>l _.
have hl : (l<j.+1)%N := ltn_ord l.
have hln : (l<=n)%N := ltnW (leq_trans hl hj).
have hsub : (j.+1-l<=n)%N := leq_trans (leq_subr l j.+1) hj.
by rewrite (hGH _ hsub) (ih l hl hln).
Qed.

(** Source for [partition_derivative_bounds_unique]:
    the sufficient recurrence specifies one
    family of constants, supporting their
    opaque use in Federer 3.1.13,
    p. 225. *)
Lemma partition_derivative_bounds_unique (R : realType) C (G V W : nat->R) :
  is_partition_derivative_bounds C G V ->
  is_partition_derivative_bounds C G W -> forall n, V n=W n.
Proof.
move=>hV hW n.
exact: (partition_derivative_bounds_initial_dependence hV hW (fun i _=>erefl _) (leqnn n)).
Qed.

(** Source for [scalar_power_quotient_product]:
    denominator powers combine in the
    derivative recurrence of Federer 3.1.13,
    p. 225. This is ordinary
    scalar arithmetic, including degree zero. *)
Lemma scalar_power_quotient_product (R : realType) (a b r : R) p q :
  (a/r^+p)*(b/r^+q)=(a*b)/r^+(p+q).
Proof. by rewrite mulrACA -invfM -exprD. Qed.

(** Source for [partition_derivative_bounds_scaled_recurrence]:
    all terms in the nth derivative
    estimate carry the same factor h(x)^(-n),
    Federer 3.1.13, p. 225. *)
Lemma partition_derivative_bounds_scaled_recurrence (R : realType)
    C (G V : nat->R) r n :
  is_partition_derivative_bounds C G V ->
  G n.+1/r^+n.+1+\sum_(j<n.+1) ('C(n.+1,n.+1-j))%:R*
    ((C*G (n.+1-j)%N/r^+(n.+1-j)%N)*(V j/r^+j))=V n.+1/r^+n.+1.
Proof.
move=>hV; rewrite hV.2 mulrDl; congr (_+_).
have he (j : 'I_n.+1) : ('C(n.+1,n.+1-j))%:R*
      ((C*G (n.+1-j)%N/r^+(n.+1-j)%N)*(V j/r^+j))=
    (C*(('C(n.+1,n.+1-j))%:R*(G (n.+1-j)%N*V j)))/r^+n.+1.
  rewrite scalar_power_quotient_product (subnK (ltnW (ltn_ord j))).
  ring.
under eq_bigr do rewrite he.
by rewrite -mulr_suml -mulr_sumr.
Qed.

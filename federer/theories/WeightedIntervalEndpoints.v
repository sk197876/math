(** Federer (1969), 4.1.12, p. 369: the
    original u_1=0, u_(k+1)=u_k+4k^(-3)
    and v_k=u_k+2k^(-3). Formal n denotes
    the printed k=n+1. Retain the literal
    finite-prefix endpoints and the exact infinite
    support interval from the original numerical sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra ring.
From Federer Require Import NonnegativeSum NonnegativeSumScale NonnegativeSequenceTail NonnegativeRealSeriesTails
  ReciprocalPowerSeriesBounds CosetLoneIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_interval_left_endpoint]:
    the original u_k, represented by its
    equivalent finite sum, Federer 4.1.12, p. 369. *)
Definition weighted_interval_left_endpoint (R:realType) n:R:=
  4*\sum_(j<n) reciprocal_power_series_weight R 3%N j.

(** Source for [weighted_interval_right_endpoint]: the
    original v_k=u_k+2k^(-3), Federer
    4.1.12, p. 369. *)
Definition weighted_interval_right_endpoint (R:realType) n:R:=
  weighted_interval_left_endpoint R n+2*reciprocal_power_series_weight R 3%N n.

(** Source for [weighted_interval_support_endpoint]: the
    original finite sum of 4k^(-3),
    giving the exact right endpoint of
    the common compact interval in Federer
    4.1.12, p. 369. Its
    numerical sum has already been proved finite. *)
Definition weighted_interval_support_endpoint (R:realType):R:=
  4*fine (nonnegative_sum setT (fun n=>(reciprocal_power_series_weight R 3%N n)%:E)).

(** Source for [weighted_interval_support_endpoint_sum]:
    the chosen finite support endpoint
    is exactly the original sum of
    4k^(-3), including its literal coefficient,
    Federer 4.1.12, p. 369. *)
Lemma weighted_interval_support_endpoint_sum (R:realType):
  (weighted_interval_support_endpoint R)%:E=
    nonnegative_sum setT (fun k=>(4*reciprocal_power_series_weight R 3%N k)%:E).
Proof.
pose a:=reciprocal_power_series_weight R 3%N.
have hNumber:nonnegative_sum setT (fun k=>(a k)%:E) \is a fin_num.
  rewrite ge0_fin_numE;last exact:nonnegative_sum_nonnegative.
  exact:reciprocal_cube_series_finite.
have hInput:(fun k=>(4*reciprocal_power_series_weight R 3%N k)%:E)=
    (fun k=>(4:R)%:E*(a k)%:E)%E.
  apply:funext=>k;by rewrite EFinM.
have ha k:(0<=(a k)%:E)%E.
  rewrite lee_fin;exact:ltW (reciprocal_power_series_weight_positive R 3%N k).
rewrite hInput (@nonnegative_sum_scale R nat setT (fun k=>(a k)%:E) 4
  (ltac:(by rewrite ler0n)) (fun k _=>ha k)).
by rewrite /weighted_interval_support_endpoint EFinM (fineK hNumber).
Qed.

(** Source for [weighted_interval_left_endpoint_zero]:
    the original u_1=0, Federer 4.1.12, p. 369. *)
Lemma weighted_interval_left_endpoint_zero (R:realType):weighted_interval_left_endpoint R 0%N=0.
Proof. by rewrite /weighted_interval_left_endpoint big_ord0 mulr0. Qed.

(** Source for [weighted_interval_left_endpoint_step]:
    the original recurrence u_(k+1)=u_k+4k^(-3),
    exactly as in Federer 4.1.12, p. 369. *)
Lemma weighted_interval_left_endpoint_step (R:realType) n:
  weighted_interval_left_endpoint R n.+1=weighted_interval_left_endpoint R n+
    4*reciprocal_power_series_weight R 3%N n.
Proof. by rewrite /weighted_interval_left_endpoint big_ord_recr /= mulrDr. Qed.

(** Source for [weighted_interval_endpoint_order]: the
    original intervals are positively oriented and
    lie strictly before the next u endpoint,
    supporting Federer 4.1.12, p. 369. *)
Lemma weighted_interval_endpoint_order (R:realType) n:
  0<=weighted_interval_left_endpoint R n /\
  weighted_interval_left_endpoint R n<weighted_interval_right_endpoint R n /\
  weighted_interval_right_endpoint R n<weighted_interval_left_endpoint R n.+1.
Proof.
have hw:=reciprocal_power_series_weight_positive R 3%N n.
have hNonnegative:0<=weighted_interval_left_endpoint R n.
  rewrite /weighted_interval_left_endpoint;apply:mulr_ge0;first by rewrite ler0n.
  apply:sumr_ge0=>j _;exact:ltW (reciprocal_power_series_weight_positive R 3%N j).
split;first exact:hNonnegative.
rewrite /weighted_interval_right_endpoint weighted_interval_left_endpoint_step.
split;lra.
Qed.

(** Source for [weighted_interval_left_endpoint_monotone]:
    the original consecutive interval endpoints
    increase, supporting disjointness of the
    phi_k supports in Federer 4.1.12,
    p. 369. *)
Lemma weighted_interval_left_endpoint_monotone (R:realType) i j:(i<=j)%N->
  weighted_interval_left_endpoint R i<=weighted_interval_left_endpoint R j.
Proof.
have hStep n:weighted_interval_left_endpoint R n<=weighted_interval_left_endpoint R n.+1.
  have[_ [hLeft hRight]]:=weighted_interval_endpoint_order R n.
  exact:ltW (lt_trans hLeft hRight).
exact:(@homo_leq R (weighted_interval_left_endpoint R) (fun a b:R=>is_true (a<=b))
  (fun x=>lexx x) (fun b a c hab hbc=>le_trans hab hbc) hStep).
Qed.

(** Source for [weighted_interval_left_endpoint_bound]:
    every original u_k lies at most
    the printed sum of 4k^(-3),
    supporting the common support interval in
    Federer 4.1.12, p. 369. *)
Lemma weighted_interval_left_endpoint_bound (R:realType) n:
  weighted_interval_left_endpoint R n<=weighted_interval_support_endpoint R.
Proof.
pose a:=reciprocal_power_series_weight R 3%N.
have ha j:0<=a j:=ltW (reciprocal_power_series_weight_positive R 3%N j).
have hFinite:=@reciprocal_cube_series_finite R.
have hNumber:nonnegative_sum setT (fun j=>(a j)%:E) \is a fin_num.
  rewrite ge0_fin_numE;last exact:nonnegative_sum_nonnegative.
  exact:hFinite.
have hBound:=@nonnegative_sum_subset R nat [set j|(j<n)%N] setT (fun j=>(a j)%:E)
  (fun _ _=>Logic.I).
rewrite (@nat_prefix_nonnegative_sum R a n ha) -(fineK hNumber) lee_fin in hBound.
exact:(ler_wpM2l (ltac:(by rewrite ler0n):0<=(4:R)) hBound).
Qed.

(** Source for [weighted_interval_mass_coefficient]: the
    original kth weighted interval has length
    coefficient k*(2k^(-3))=2k^(-2), supporting
    M(S)=2 sum k^(-2) in Federer
    4.1.12, p. 369. *)
Lemma weighted_interval_mass_coefficient (R:realType) n:
  (n.+1)%:R*(weighted_interval_right_endpoint R n-weighted_interval_left_endpoint R n)=
    2*reciprocal_power_series_weight R 2%N n.
Proof.
rewrite /weighted_interval_right_endpoint addrAC subrr add0r /reciprocal_power_series_weight.
pose k:R:=(n.+1)%:R.
have hNonzero:k!=0 by rewrite /k pnatr_eq0.
change (k*(2*k^-1^+3)= 2*k^-1^+2).
by rewrite mulrCA exprS (mulrA k k^-1 (k^-1^+2)) (mulfV hNonzero) mul1r.
Qed.

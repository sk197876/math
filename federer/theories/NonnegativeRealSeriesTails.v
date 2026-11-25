(** Federer (1969), 2.1.1(13), p. 53,
    and 2.3.9, p. 79, used
    in 4.1.12, p. 369:
    finite nonnegative real series have real
    tails with the exact difference and
    prefix identities. Reuse the original numerical sum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSequenceTail NonnegativeSequenceTailStep
  CosetLoneIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_real_series_tail]: the
    real value of the original numerical
    tail, supporting the actual series in
    Federer 4.1.12, p. 369.
    Laws below require proved summability. *)
Definition nonnegative_real_series_tail (R:realType) (a:nat->R) n:R:=
  fine (nonnegative_sequence_tail (fun k=>(a k)%:E) n).

Section NonnegativeRealSeriesTails.
Variable R:realType.
Variable a:nat->R.
Hypothesis ha:forall k,0<=a k.
Hypothesis hFinite:(nonnegative_sum setT (fun k=>(a k)%:E)< +oo)%E.
Local Notation A := (fun k=>(a k)%:E).
Local Notation tail := (nonnegative_real_series_tail a).

(** Source for [nonnegative_real_series_tail_value]:
    the original extended tail equals its
    actual finite real value, supporting
    Federer 4.1.12, p. 369. *)
Lemma nonnegative_real_series_tail_value n:
  nonnegative_sequence_tail A n=(tail n)%:E.
Proof. rewrite /nonnegative_real_series_tail;by rewrite fineK //;exact:nonnegative_sequence_tail_finite hFinite n. Qed.

(** Source for [nonnegative_real_series_tail_nonnegative]:
    the real mass tails are nonnegative,
    supporting Federer 4.1.12, p. 369. *)
Lemma nonnegative_real_series_tail_nonnegative n:0<=tail n.
Proof.
have h:=@nonnegative_sequence_tail_nonnegative R A n.
by rewrite nonnegative_real_series_tail_value lee_fin in h.
Qed.

(** Source for [nonnegative_real_series_tail_step]:
    subtracting consecutive original tails gives
    exactly the first term, supporting the
    series in Federer 4.1.12, p. 369. *)
Lemma nonnegative_real_series_tail_step n:tail n-tail n.+1=a n.
Proof.
have hAE k:(0<=A k)%E by rewrite lee_fin.
have h:=@nonnegative_sequence_tail_step R A n hAE.
rewrite !nonnegative_real_series_tail_value -EFinD in h.
have hReal:=EFin_inj h;by rewrite hReal addrK.
Qed.

(** Source for [nonnegative_real_series_tail_small]:
    the exact original real tails tend
    to zero, supporting convergence in Federer
    4.1.12, p. 369. *)
Lemma nonnegative_real_series_tail_small epsilon:
  0<epsilon->exists N,forall k,(N<=k)%N->tail k<epsilon.
Proof.
move=>hEpsilon.
have hAE k:(0<=A k)%E by rewrite lee_fin.
have[N hN]:=@nonnegative_sequence_tail_small R A hAE hFinite epsilon hEpsilon.
exists N=>k hNk;have h:=hN k hNk.
by rewrite nonnegative_real_series_tail_value lte_fin in h.
Qed.

(** Source for [nonnegative_real_series_prefix_tail]:
    the original sum is exactly its
    finite prefix plus the remaining real
    tail, supporting the printed mass and
    support sums in Federer 4.1.12, p. 369. *)
Lemma nonnegative_real_series_prefix_tail n:
  nonnegative_sum setT A=((\sum_(k<n) a k)+tail n)%:E.
Proof.
have hAE k:(0<=A k)%E by rewrite lee_fin.
rewrite (nonnegative_sequence_prefix_tail n hAE)
  (@nat_prefix_nonnegative_sum R a n ha) nonnegative_real_series_tail_value EFinD.
by [].
Qed.
End NonnegativeRealSeriesTails.

(** Federer (1969), proof of 2.5.2, p. 93, final limiting paragraph:
    truncations at n epsilon increase to f, and f-min(f,epsilon) increases
    to f as epsilon decreases to zero. These supporting pointwise
    order-limit proofs use only Archimedean real arithmetic. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp MonotoneDaniellIntegralUP
  ExtendedRealOrderLimit ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_step_truncations_increase]: f_(n epsilon) increases to
    f in Federer 2.5.2, p. 93 A fixed natural offset includes the
    neighbouring truncations in the same display. *)
Lemma real_step_truncations_increase (R : realType) (X : Type)
    (f : X -> R) (e : R) (k : nat) : (0 < e)%R ->
  real_functions_increase_to (fun n x => Order.min (f x) (((n+k)%:R)*e)%R) f.
Proof.
move=> he x; split.
- move=> n m hnm; rewrite lee_fin; apply: real_minimum_ceiling_monotone.
  by rewrite (ler_pM2r he) ler_nat leq_add2r.
- pose N := Num.bound `|f x/e|%R.
  have hN : (f x/e < N%:R)%R := le_lt_trans (ler_norm _) (archi_boundP (normr_ge0 _)).
  have hNe : (f x < N%:R*e)%R by rewrite -ltr_pdivrMr.
  have hbound n : (N <= n)%N -> (f x <= ((n+k)%:R)*e)%R.
    move=> hn; apply: le_trans (ltW hNe) _.
    rewrite (ler_pM2r he) ler_nat; exact: leq_trans hn (leq_addr k n).
  split; move=> a ha; exists N=> n hn; by rewrite (min_l (hbound n hn)).
Qed.

(** Source for [positive_reciprocal_nat_antitone]: supporting choice
    epsilon_n= 1/(n+1) in the final limit of Federer 2.5.2, p. 93 *)
Lemma positive_reciprocal_nat_antitone (R : realType) n m :
  (n <= m)%N -> (((m.+1)%:R : R)^-1 <= ((n.+1)%:R)^-1)%R.
Proof.
move=> hnm.
have hpn : (0 < (n.+1)%:R :> R)%R by rewrite ltr0n.
have hpm : (0 < (m.+1)%:R :> R)%R by rewrite ltr0n.
by rewrite (@lef_pV2 R ((m.+1)%:R) ((n.+1)%:R) hpm hpn) ler_nat.
Qed.

(** Source for [real_reciprocal_truncation_tails_increase]: f-f_epsilon
    increases to f as epsilon decreases to zero in Federer 2.5.2, p. 93 The
    chosen reciprocal sequence is cofinal among positive cutoffs. The
    pointwise nonnegativity of f is retained. *)
Lemma real_reciprocal_truncation_tails_increase (R : realType) (X : Type)
    (f : X -> R) : function_nonnegative f ->
  real_functions_increase_to
    (fun n x => (f x-Order.min (f x) ((n.+1)%:R)^-1)%R) f.
Proof.
move=> hf x; split.
- move=> n m hnm; rewrite lee_fin lerD2l lerN2.
  apply: real_minimum_ceiling_monotone; exact: positive_reciprocal_nat_antitone hnm.
- split.
  + move=> a ha; case: a ha=> [r| |] ha.
    * have hr : (0 < f x-r)%R by rewrite subr_gt0; exact ha.
      have [N hN] := positive_reciprocal_nat_small hr.
      exists N=> n hn; rewrite lte_fin ltrBrDl.
      have hsmall : (((n.+1)%:R)^-1 < f x-r)%R.
        exact: le_lt_trans (@positive_reciprocal_nat_antitone R N n hn) hN.
      have hmin : (Order.min (f x) ((n.+1)%:R)^-1 < f x-r)%R.
        apply: le_lt_trans _ hsmall; by rewrite ge_min lexx orbT.
      by move: hmin; rewrite ltrBrDr addrC.
    * by move: ha; rewrite ltNge leey.
    * exists 0%N=> n _; exact: ltNyr.
  + move=> b hb; exists 0%N=> n _; apply: le_lt_trans _ hb.
    rewrite lee_fin lerBlDr lerDl le_min (hf x) invr_ge0 ler0n.
    by [].
Qed.

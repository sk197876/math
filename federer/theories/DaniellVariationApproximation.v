(** Federer (1969), 2.5.5, p. 97: select g_n in L+ below f with mu(g_n)
    tending to mu+(f). The supremum law gives approximants with reciprocal
    error; the selection is used only to prove existence of a sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariationBounds
  ExtendedRealOrderLimit ExtendedRealReciprocalBounds RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_variation_strict_approximation]: supporting choice
    arbitrarily near the supremum in Federer 2.5.5, p. 97 No attainment of
    the supremum is assumed. *)
Lemma daniell_variation_strict_approximation (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) (e : R) :
  positive_function_lattice L f -> (0 < e)%R ->
  exists k, lattice_positive_order_interval L f k /\ (P f-e < A k)%R.
Proof.
move=> hf he; apply: contrapT=> hn.
have hb : (P f <= P f-e)%R.
  apply: (@daniell_positive_variation_least R X L A P hP f _ hf)=> k hk.
  rewrite leNgt; apply/negP=> hlt; apply: hn; by exists k.
have hs : (P f-e < P f)%R by rewrite ltrBlDr ltrDl.
by move: hs; rewrite ltNge hb.
Qed.

(** Source for [daniell_variation_approximating_sequence]: exact sequence
    g_n used in the last paragraph of Federer 2.5.5, p. 97 The sequence
    stays between zero and f everywhere, while its functional values
    converge without a monotonicity requirement. *)
Theorem daniell_variation_approximating_sequence (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) :
  positive_function_lattice L f -> exists g : nat -> X -> R,
    (forall n, lattice_positive_order_interval L f (g n)) /\
    extended_order_limit (fun n => (A (g n))%:E) (P f)%:E.
Proof.
move=> hf.
have happ n : exists k, lattice_positive_order_interval L f k /\
    (P f-(n.+1%:R)^-1 < A k)%R.
  apply: (@daniell_variation_strict_approximation R X L A P hP f _ hf).
  by rewrite invr_gt0 ltr0n.
pose g n := projT1 (cid (happ n)).
have hg n := projT2 (cid (happ n)).
exists g; split; first by move=> n; exact: (hg n).1.
apply: real_error_extended_order_limit=> e he.
have [N hN] := @positive_reciprocal_nat_small R e he.
exists N=> n hn.
have hgn : (A (g n) <= P f)%R := @daniell_positive_variation_upper R X L A P hP f _ hf (hg n).1.
rewrite ler0_norm; last by rewrite subr_le0.
rewrite opprB.
have herror : (P f-A (g n) < (n.+1%:R)^-1)%R.
  rewrite ltrBlDr addrC -ltrBlDr; exact: (hg n).2.
have hrec : ((n.+1%:R)^-1 <= (N.+1%:R)^-1 :> R)%R.
  have hpn : (0 < n.+1%:R :> R)%R by rewrite ltr0n.
  have hpN : (0 < N.+1%:R :> R)%R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hpn hpN) ler_nat.
exact: lt_trans (lt_le_trans herror hrec) hN.
Qed.

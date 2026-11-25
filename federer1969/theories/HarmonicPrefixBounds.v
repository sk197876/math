(** Consequences of the sealed harmonic-prefix laws supporting
    Federer (1969), 2.8.20, p. 152. Cesari1939
    Lemma III, p. 306, requires a sufficiently large
    harmonic partial sum. Downstream arguments use only the
    specification in HarmonicPrefixUP.v, not the reused private
    construction. Source comparisons: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import HarmonicPrefixUP HarmonicPrefixSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [harmonic_partial_sum]: the finite harmonic
    sum supporting the construction in Federer 2.8.20,
    p. 152; Cesari1939 Lemma III, p. 306. *)
Definition harmonic_partial_sum (R : realType) := @HarmonicPrefix.value R.

(** Source for [harmonic_partial_sumE]: the term formula for
    the finite harmonic sum supporting Federer 2.8.20,
    p. 152; Cesari1939 Lemma III, p. 306. *)
Lemma harmonic_partial_sumE (R : realType) N :
  harmonic_partial_sum R N = \sum_(i < N) ((i.+1)%:R : R)^-1.
Proof. exact: harmonic_prefix_equation (HarmonicPrefix.laws R) N. Qed.

(** Source for [harmonic_partial_sums_unbounded]: the choice
    of a harmonic partial sum exceeding any prescribed bound
    in Cesari1939 Lemma III, p. 306, supporting the
    Bohr construction cited by Federer 2.8.20, p. 152.
    The proof uses the sealed dyadic bound and the Archimedean
    property, retaining a positive finite index. *)
Lemma harmonic_partial_sums_unbounded (R : realType) (C : R) :
  exists N : nat, (0 < N)%N /\ C < harmonic_partial_sum R N.
Proof.
pose k := Num.bound (2*`|C|).
have hk : 2*`|C| < k%:R by apply: archi_boundP; apply: mulr_ge0; [by rewrite ler0n|exact: normr_ge0].
have hC : C < k%:R/2.
  rewrite ltr_pdivlMr ?ltr0n //.
  apply: le_lt_trans _ hk; rewrite mulrC; apply: ler_wpM2l; first by rewrite ler0n.
  exact: ler_norm.
exists (2^k)%N; split; first by rewrite expn_gt0.
exact: lt_le_trans hC (harmonic_prefix_dyadic_lower (HarmonicPrefix.laws R) k).
Qed.

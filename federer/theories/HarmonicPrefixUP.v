(** Supporting finite harmonic sums for the Bohr construction cited in
    Federer (1969), 2.8.20, p. 152. Cesari, Sul teorema di densita in senso
    forte (1939), section II.4, Lemma III, p. 306, chooses a finite harmonic
    sum greater than the reciprocal of a prescribed positive error. The
    abstract laws below give that finite sum and an elementary dyadic lower
    bound. They do not assert that Federer states this supporting bound
    separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_harmonic_prefix]: specification supporting
    the harmonic cutoff in Cesari1939 Lemma III, p. 306,
    for Federer 2.8.20, p. 152. Each term is the
    reciprocal of its positive natural index. The lower bound
    supplies unboundedness by grouping successive dyadic blocks. *)
Record is_harmonic_prefix (R : realType) (H : nat -> R) : Prop := {
  (** Source for [harmonic_prefix_equation]: the finite harmonic
      sum used in Cesari1939 Lemma III, p. 306, supporting
      Federer 2.8.20, p. 152. Formal term i is 1/(i+1). *)
  harmonic_prefix_equation : forall N, H N = \sum_(i < N) ((i.+1)%:R : R)^-1;
  (** Source for [harmonic_prefix_dyadic_lower]: elementary
      supporting divergence bound for the choice of r in
      Cesari1939 Lemma III, p. 306, for Federer
      2.8.20, p. 152. It is proved locally, not assumed. *)
  harmonic_prefix_dyadic_lower : forall k, k%:R / 2 <= H (2^k)%N
}.

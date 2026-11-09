(** Federer (1969), 3.4.5, pp. 320–321: the empty
    germ satisfies the literal irreducibility test. Proper
    prime ideals and unique irreducible component families
    therefore require the nonempty convention stated separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP SetGermLaws SetGermFiniteUnion
  SetGermBoundary CommutativeIdealUP GermVanishingSealed AnalyticIdealPropriety
  AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section EmptyBoundary.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T a).
Local Notation empty:=(@set_germ T a set0).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].

(** Source for [analytic_empty_germ_not_proper_prime]: the
    literal irreducible empty germ has the whole vanishing
    ideal, which is not a proper prime ideal. This is
    the convention qualification to 3.4.5, p. 320. *)
Theorem analytic_empty_germ_not_proper_prime:
  @is_union_irreducible_analytic_germ R X NX hNX a empty /\
  ~@is_prime_commutative_ideal A (@AnalyticSetIdeal.value R X NX hNX a empty).
Proof.
split;first exact:analytic_empty_germ_union_irreducible.
move=>[_ [hProper _]];apply:hProper.
exact:(analytic_set_ideal_contains_one empty).2 (erefl _).
Qed.

(** Source for [analytic_empty_germ_two_literal_families]: the
    empty family and the singleton empty-germ family have
    the same union, consist of literal irreducible germs,
    and are distinct families. Both are antichains. This
    explains the nonempty-component qualification to the
    uniqueness sentence of 3.4.5, p. 321. *)
Theorem analytic_empty_germ_two_literal_families:
  @set_germ_finite_union T a [::]=empty /\
  @set_germ_finite_union T a [::empty]=empty /\
  ([set beta:G|beta \in [::]]<>[set beta:G|beta \in [::empty]]) /\
  forall K:seq G,(K=[::] \/K=[::empty]) ->
    (forall beta,beta \in K ->@is_union_irreducible_analytic_germ R X NX hNX a beta) /\
    forall beta gamma,beta \in K ->gamma \in K ->beta=gamma.
Proof.
split;first by [].
split.
- by rewrite /set_germ_finite_union /= set_germ_union_empty.
- split.
  + move=>hEqual.
    have hMember:[set beta:G|beta \in [::empty]] empty by rewrite /= in_cons eqxx.
    by rewrite -hEqual /= in hMember.
  + move=>K [->|->];split.
    * by move=>beta;rewrite in_nil.
    * by move=>beta gamma;rewrite in_nil.
    * move=>beta;rewrite mem_seq1=>/eqP ->;exact:analytic_empty_germ_union_irreducible.
    * by move=>beta gamma;rewrite !mem_seq1=>/eqP -> /eqP ->.
Qed.
End EmptyBoundary.

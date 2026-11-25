(** Federer (1969), 2.10.28(4), pp. 192–193: abstract laws for the common
    child length s with h(s)=h(d)/n and 0<s<d/n. The parent length d must be
    positive, as stated. This nondegeneracy hypothesis is absent from the
    printed Federer statement. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_cantor_split_radius]: direct scalar
    laws in 2.10.28(4), p. 192,
    before constructing the equal-cost intervals.
    The laws specify the child length, which
    will be proved to exist for positive
    parent length and n>=2. *)
Record is_cantor_split_radius (R : realType) (h : R -> R) (d : R) (n : nat) (s : R) : Prop := {
  (** Source for [cantor_split_radius_bounds]: direct
      0<s<diam(J)/n conclusion in 2.10.28(4),
      p. 192, under the corrected nondegenerate
      parent hypothesis. *)
  cantor_split_radius_bounds : 0<s /\ s<d/n%:R;
  (** Source for [cantor_split_radius_cost]: direct
      h(s)=zeta(J)/n law in 2.10.28(4),
      p. 192, where d=diam(J). *)
  cantor_split_radius_cost : h s=h d/n%:R
}.

(** Source for [cantor_split_radius_unique]: supporting uniqueness of the
    equal-cost child length used in 2.10.28(4), pp. 192–193, from strict
    growth of the gauge *)
Lemma cantor_split_radius_unique (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) d n s t :
  is_cantor_split_radius h d n s -> is_cantor_split_radius h d n t -> s=t.
Proof.
move=> hs ht; case: (ltgtP s t)=> [hst|hts|heq]; last exact heq.
- have hh := concave_interval_gauge_strictly_increasing hg (ltW (cantor_split_radius_bounds hs).1) hst.
  by rewrite (cantor_split_radius_cost hs) (cantor_split_radius_cost ht) ltxx in hh.
- have hh := concave_interval_gauge_strictly_increasing hg (ltW (cantor_split_radius_bounds ht).1) hts.
  by rewrite (cantor_split_radius_cost hs) (cantor_split_radius_cost ht) ltxx in hh.
Qed.

(** Source for [zero_parent_cantor_split_impossible]: local
    degenerate-parent counterexample to the unqualified 0<s<diam(J)/n
    conclusion in 2.10.28(4), p. 192. For the singleton interval d=0 no
    child length satisfies those laws, regardless of n. *)
Lemma zero_parent_cantor_split_impossible (R : realType) (h : R -> R) n s :
  ~is_cantor_split_radius h 0 n s.
Proof.
move=> hs; have [hpos hbound] := cantor_split_radius_bounds hs.
rewrite mul0r in hbound; lra.
Qed.

(** Federer (1969), 2.10.28(1), proof p. 192: the finite clipping estimate
    in endpoint coordinates. Treat a degenerate test interval, a member
    containing the whole test interval, and the remaining two-boundary case
    separately. No enumeration order or nondegenerate member hypothesis is
    imposed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals lra.
From Federer Require Import ConcaveIntervalGaugeUP FiniteIntervalBoundaryUP FiniteIntervalBoundaries
  IntervalClipLength FiniteIntervalClippingSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [degenerate_interval_clip_length]: supporting
    zero-length test interval in 2.10.28(1),
    pp. 191–192. Its intersection with any
    interval has diameter zero, even if empty. *)
Lemma degenerate_interval_clip_length (R : realType) (a c d : R) :
  real_interval_clip_length a a c d=0.
Proof.
have hmin : Order.min a d<=a by rewrite ge_min lexx.
have hmax : a<=Order.max a c by rewrite le_max lexx.
have hlen : Order.min a d-Order.max a c<=0 by lra.
by rewrite /real_interval_clip_length (max_l hlen).
Qed.

(** Source for [finite_concave_interval_clipping_bound]: supporting
    endpoint-coordinate form of 2.10.28(1),
    pp. 191–192. The whole-member envelope
    is exactly the last condition defining
    special; the stronger clipped bound is
    proved from it and concavity. *)
Theorem finite_concave_interval_clipping_bound (R : realType) (I : choiceType)
    (h : R -> R) (hg : is_concave_interval_gauge h) (F : {fset I}) (l r : I -> R) (a b : R) :
  a<=b -> (forall i, i \in F -> l i<=r i) ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  (forall u v, u<=v -> \sum_(i <- F | `[< u<=l i /\ r i<=v >]) h (r i-l i)<=h (v-u)) ->
  \sum_(i <- F) h (real_interval_clip_length a b (l i) (r i))<=h (b-a).
Proof.
move=> hab hord hdis henv.
case: (ltP a b)=> [habp|hba]; last first.
  have heq : a=b by apply/eqP; rewrite eq_le hab hba.
  subst b.
  have hz : (\sum_(i <- F) h (real_interval_clip_length a a (l i) (r i)))=0.
    apply: big1=> i _; by rewrite degenerate_interval_clip_length (interval_gauge_zero hg).
  by rewrite hz subrr (interval_gauge_zero hg).
case: (pselect (exists i, i \in F /\ l i<=a /\ b<=r i))=> [[i [hi [hlia hbri]]]|hnone].
- have hclip : real_interval_clip_length a b (l i) (r i)=b-a.
    rewrite /real_interval_clip_length (min_l hbri) (max_l hlia) max_r //; by rewrite subr_ge0.
  have hz : (\sum_(j <- (F `\ i)%fset) h (real_interval_clip_length a b (l j) (r j)))=0.
    rewrite big_seq; apply: big1=> j hj.
    have /andP[hji hjF] : (j!=i) && (j \in F) by move: hj; rewrite !inE.
    case: (hdis j i hjF hi hji)=> hgap.
    + have hrja : r j<=a := le_trans (ltW hgap) hlia.
      by rewrite (@interval_clip_length_left_zero R a b (l j) (r j) hrja) (interval_gauge_zero hg).
    + have hblj : b<=l j := le_trans hbri (ltW hgap).
      by rewrite (@interval_clip_length_right_zero R a b (l j) (r j) hblj) (interval_gauge_zero hg).
  by rewrite (big_fsetD1 _ hi) /= hz hclip addr0.
- have hno i (hi : i \in F) (hlia : l i<=a) (hbri : b<=r i) : False.
    apply: hnone; exists i; by split=> //; split.
  have [L [W [v0 [v1 [w0 [w1 hb]]]]]] :=
    @finite_interval_boundary_exists R I F l r a b hab hdis hno.
  have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
  have hbig : v0<=w1 := le_trans hva (le_trans hav (le_trans hvw (le_trans hwb hbw))).
  exact: (@finite_interval_clipping_boundary_bound R I h hg F l r a b L W v0 v1 w0 w1 hb
    habp hord hdis (henv v0 w1 hbig)).
Qed.

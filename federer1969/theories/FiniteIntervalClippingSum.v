(** Federer (1969), 2.10.28(1), proof p. 192: sum the exact boundary
    accounting and apply the special-family whole-interval bound to the
    enlarged test interval. The two concave enlargement inequalities cancel
    the losses. Optional zero-cost endpoints replace its preliminary
    shrinkage when an endpoint meets no member. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalClipping FiniteIntervalBoundaryUP
  IntervalClipLength FiniteIntervalClippingPointwise FiniteOptionalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [finite_interval_boundary_loss]: supporting
    zeta(V)-zeta(T intersect V) boundary term
    in the proof of 2.10.28(1), p. 192.
    An absent boundary member has zero loss. *)
Definition finite_interval_boundary_loss (R : realType) (I : choiceType)
    (h : R -> R) (l r : I -> R) (a b : R) (V : option I) :=
  match V with Some i=>h (r i-l i)-h (real_interval_clip_length a b (l i) (r i)) | None=>0 end.

(** Source for [finite_interval_boundary_losses]: supporting
    identification of the two boundary losses
    with the overlap lengths in the two
    displays of 2.10.28(1), p. 192.
    Degenerate placeholders give zero without
    any extra positivity assumption. *)
Lemma finite_interval_boundary_losses (R : realType) (I : choiceType)
    (h : R -> R) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) :
  finite_interval_boundary_loss h l r a b L=h (v1-v0)-h (v1-a) /\
  finite_interval_boundary_loss h l r a b W=h (w1-w0)-h (b-w0).
Proof.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
have hvb : v1<=b := le_trans hvw hwb.
have haw : a<=w0 := le_trans hav hvw.
split.
- have hL := finite_interval_boundary_left hb.
  case hopt : L=> [i|] in hL *.
  + have [_ [hv0 hv1]] := hL.
    by rewrite /finite_interval_boundary_loss -hv0 -hv1
      (@interval_clip_length_left_boundary R a b v0 v1 hva hav hvb).
  + by rewrite /finite_interval_boundary_loss hL.1 hL.2 !subrr.
- have hW := finite_interval_boundary_right hb.
  case hopt : W=> [i|] in hW *.
  + have [_ [hw0 hw1]] := hW.
    by rewrite /finite_interval_boundary_loss -hw0 -hw1
      (@interval_clip_length_right_boundary R a b w0 w1 haw hwb hbw).
  + by rewrite /finite_interval_boundary_loss hW.1 hW.2 !subrr.
Qed.

(** Source for [finite_interval_clipping_sum_identity]: supporting
    exact finite cost identity before the final
    inequality in 2.10.28(1), p. 192.
    Keep every member's contribution once and
    separate only the two actual boundary losses. *)
Lemma finite_interval_clipping_sum_identity (R : realType) (I : choiceType)
    (h : R -> R) (hg : is_concave_interval_gauge h) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) :
  a<b -> (forall i, i \in F -> l i<=r i) ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  \sum_(i <- F | `[< v0<=l i /\ r i<=w1 >]) h (r i-l i)=
    \sum_(i <- F) h (real_interval_clip_length a b (l i) (r i))+
    finite_interval_boundary_loss h l r a b L+finite_interval_boundary_loss h l r a b W.
Proof.
move=> hab hord hdis.
pose loss i := h (r i-l i)-h (real_interval_clip_length a b (l i) (r i)).
have hLmem i (hi : L=Some i) : i \in F.
  have hx := finite_interval_boundary_left hb; rewrite hi in hx; exact hx.1.
have hWmem i (hi : W=Some i) : i \in F.
  have hx := finite_interval_boundary_right hb; rewrite hi in hx; exact hx.1.
have hLsum := @finite_optional_real_sum R I F L loss hLmem.
have hWsum := @finite_optional_real_sum R I F W loss hWmem.
rewrite big_mkcond.
transitivity (\sum_(i <- F) (h (real_interval_clip_length a b (l i) (r i))+
    (if L==Some i then loss i else 0)+(if W==Some i then loss i else 0))).
- apply: eq_big_seq=> i hi.
  exact: (@finite_interval_clipping_cost_identity R I h hg F l r a b L W v0 v1 w0 w1 hb i hab hord hdis hi).
- by rewrite !big_split hLsum hWsum /finite_interval_boundary_loss /loss.
Qed.

(** Source for [finite_interval_clipping_boundary_bound]: supporting
    last enlargement comparison in the proof
    of 2.10.28(1), p. 192. Only the
    whole-member cost bound on the enlarged
    interval is used at this step. *)
Lemma finite_interval_clipping_boundary_bound (R : realType) (I : choiceType)
    (h : R -> R) (hg : is_concave_interval_gauge h) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) :
  a<b -> (forall i, i \in F -> l i<=r i) ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  \sum_(i <- F | `[< v0<=l i /\ r i<=w1 >]) h (r i-l i)<=h (w1-v0) ->
  \sum_(i <- F) h (real_interval_clip_length a b (l i) (r i))<=h (b-a).
Proof.
move=> hab hord hdis hbound.
have heq := @finite_interval_clipping_sum_identity R I h hg F l r a b L W v0 v1 w0 w1 hb hab hord hdis.
have [hleft hright] := finite_interval_boundary_losses h hb.
rewrite heq hleft hright in hbound.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
have hcap := @concave_interval_two_boundary_extension R h hg a b v0 v1 w0 w1 hva hav hvw hwb hbw.
lra.
Qed.

(** Federer (1969), 2.10.28(1), proof p. 192: supporting pointwise
    accounting for the two boundary members. Intervals missing the test
    interval contribute zero, interior members retain their whole cost, and
    only the two endpoint members incur clipping losses. The boundary
    specification handles missing members by zero-cost point placeholders. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals lra.
From Federer Require Import ConcaveIntervalGaugeUP FiniteIntervalBoundaryUP IntervalClipLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [finite_interval_boundary_different]: supporting
    distinctness of the two actual endpoint
    members for a nondegenerate test interval
    in 2.10.28(1), p. 192. *)
Lemma finite_interval_boundary_different (R : realType) (I : choiceType) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) i :
  a<b -> L=Some i -> W!=Some i.
Proof.
move=> hab hL; apply/negP=> /eqP hW.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
have hl := finite_interval_boundary_left hb; rewrite hL in hl.
have hr := finite_interval_boundary_right hb; rewrite hW in hr.
have [_ [hv0 hv1]] := hl; have [_ [hw0 hw1]] := hr.
rewrite hv0 hv1 hw0 hw1 in hva hav hvw hwb hbw; lra.
Qed.

(** Source for [finite_interval_boundary_left_exclusion]:
    supporting exclusion from the enlarged test
    interval of an unselected member lying left
    of [a,b], in 2.10.28(1), p. 192. *)
Lemma finite_interval_boundary_left_exclusion (R : realType) (I : choiceType) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) i :
  (forall j, j \in F -> l j<=r j) ->
  (forall j k, j \in F -> k \in F -> j!=k -> r j<l k \/ r k<l j) ->
  i \in F -> L!=Some i -> r i<a -> l i<v0.
Proof.
move=> hord hdis hi hne hria.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
have hL := finite_interval_boundary_left hb.
case hopt : L=> [j|] in hL.
- have [hj [hv0 hv1]] := hL.
  have hji : j!=i by move: hne; rewrite hopt /=.
  have horder := hord i hi.
  have hrja : a<=r j by rewrite -hv1.
  case: (hdis j i hj hi hji)=> hgap.
  + exfalso; lra.
  + rewrite hv0; exact: le_lt_trans horder hgap.
- rewrite hL.1; exact: le_lt_trans (hord i hi) hria.
Qed.

(** Source for [finite_interval_boundary_right_exclusion]:
    supporting exclusion from the enlarged test
    interval of an unselected member lying right
    of [a,b], in 2.10.28(1), p. 192. *)
Lemma finite_interval_boundary_right_exclusion (R : realType) (I : choiceType) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) i :
  (forall j, j \in F -> l j<=r j) ->
  (forall j k, j \in F -> k \in F -> j!=k -> r j<l k \/ r k<l j) ->
  i \in F -> W!=Some i -> b<l i -> w1<r i.
Proof.
move=> hord hdis hi hne hbli.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
have hW := finite_interval_boundary_right hb.
case hopt : W=> [j|] in hW.
- have [hj [hw0 hw1]] := hW.
  have hji : j!=i by move: hne; rewrite hopt /=.
  have horder := hord i hi.
  have hljb : l j<=b by rewrite -hw0.
  case: (hdis j i hj hi hji)=> hgap.
  + rewrite hw1; exact: lt_le_trans hgap horder.
  + exfalso; lra.
- rewrite hW.2; exact: lt_le_trans hbli (hord i hi).
Qed.

(** Source for [finite_interval_boundary_interior]: supporting
    fact that every intersecting member except
    the two endpoint members lies wholly in
    the test interval, in 2.10.28(1), p. 192. *)
Lemma finite_interval_boundary_interior (R : realType) (I : choiceType) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) i :
  i \in F -> L!=Some i -> W!=Some i -> a<=r i -> l i<=b -> a<=l i /\ r i<=b.
Proof.
move=> hi hL hW hari hlib; split.
- case: (leP a (l i))=> // hlia.
  have he := finite_interval_boundary_left_detection hb hi (ltW hlia) hari.
  by rewrite he eqxx in hL.
- case: (leP (r i) b)=> // hbri.
  have he := finite_interval_boundary_right_detection hb hi hlib (ltW hbri).
  by rewrite he eqxx in hW.
Qed.

(** Source for [finite_interval_clipping_cost_identity]: supporting
    exact accounting before summing the enlargement
    argument in 2.10.28(1), p. 192.
    The whole cost in the enlarged interval
    equals the clipped cost plus a loss
    only when the index is an actual
    boundary member. No positive cost is
    assigned to absent boundary members. *)
Lemma finite_interval_clipping_cost_identity (R : realType) (I : choiceType)
    (h : R -> R) (hg : is_concave_interval_gauge h) F l r a b L W v0 v1 w0 w1
    (hb : @is_finite_interval_boundary R I F l r a b L W v0 v1 w0 w1) i :
  a<b -> (forall j, j \in F -> l j<=r j) ->
  (forall j k, j \in F -> k \in F -> j!=k -> r j<l k \/ r k<l j) ->
  i \in F ->
  (if `[< v0<=l i /\ r i<=w1 >] then h (r i-l i) else 0)=
    h (real_interval_clip_length a b (l i) (r i))+
    (if L==Some i then h (r i-l i)-h (real_interval_clip_length a b (l i) (r i)) else 0)+
    (if W==Some i then h (r i-l i)-h (real_interval_clip_length a b (l i) (r i)) else 0).
Proof.
move=> hab hord hdis hi.
have [hva [hav [hvw [hwb hbw]]]] := finite_interval_boundary_order hb.
case: (eqVneq L (Some i))=> [heL|hneL].
- have hneW := finite_interval_boundary_different hb hab heL.
  have hL := finite_interval_boundary_left hb; rewrite heL in hL.
  have [_ [hv0 hv1]] := hL.
  have hinc : v0<=l i /\ r i<=w1.
    rewrite -hv0 -hv1; split; first exact: lexx.
    exact: le_trans hvw (le_trans hwb hbw).
  rewrite (asboolT hinc) (negbTE hneW); lra.
case: (eqVneq W (Some i))=> [heW|hneW].
- have hW := finite_interval_boundary_right hb; rewrite heW in hW.
  have [_ [hw0 hw1]] := hW.
  have hinc : v0<=l i /\ r i<=w1.
    rewrite -hw0 -hw1; split; last exact: lexx.
    exact: le_trans hva (le_trans hav hvw).
  rewrite (asboolT hinc); lra.
rewrite !addr0.
case: (ltP (r i) a)=> [hria|hari].
- have hl := finite_interval_boundary_left_exclusion hb hord hdis hi hneL hria.
  have hnot : ~ (v0<=l i /\ r i<=w1) by move=> [hh _]; lra.
  by rewrite (asboolF hnot) (@interval_clip_length_left_zero R a b (l i) (r i) (ltW hria)) (interval_gauge_zero hg).
case: (ltP b (l i))=> [hbli|hlib].
- have hr := finite_interval_boundary_right_exclusion hb hord hdis hi hneW hbli.
  have hnot : ~ (v0<=l i /\ r i<=w1) by move=> [_ hh]; lra.
  by rewrite (asboolF hnot) (@interval_clip_length_right_zero R a b (l i) (r i) (ltW hbli)) (interval_gauge_zero hg).
have [hali hrib] := finite_interval_boundary_interior hb hi hneL hneW hari hlib.
have hinc : v0<=l i /\ r i<=w1.
  split; [exact: le_trans hva hali | exact: le_trans hrib hbw].
by rewrite (asboolT hinc) (@interval_clip_length_full R a b (l i) (r i) hali (hord i hi) hrib).
Qed.

(** Federer (1969), 2.10.28(1), proof p. 192: existence of the boundary data
    specified in FiniteIntervalBoundaryUP.v. Disjointness makes each
    endpoint member unique. When none exists, its point endpoint is a
    zero-cost placeholder. No selected construction is exposed or unfolded;
    the lemma provides witnesses of the abstract laws for use by existential
    elimination. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals lra.
From Federer Require Import FiniteIntervalBoundaryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [finite_disjoint_endpoint_member_unique]:
    supporting uniqueness of a closed family
    member through an endpoint in 2.10.28(1),
    p. 192. Full-set disjointness includes
    the endpoints, so two such members coincide. *)
Lemma finite_disjoint_endpoint_member_unique (R : realType) (I : choiceType) (F : {fset I})
    (l r : I -> R) x i j :
  (forall u v, u \in F -> v \in F -> u!=v -> r u<l v \/ r v<l u) ->
  i \in F -> j \in F -> l i<=x -> x<=r i -> l j<=x -> x<=r j -> i=j.
Proof.
move=> hdis hi hj hil hir hjl hjr; case: (eqVneq i j)=> // hij.
case: (hdis i j hi hj hij)=> hgap; exfalso; lra.
Qed.

(** Source for [finite_interval_left_boundary_exists]:
    supporting left endpoint member or zero-cost
    point placeholder for 2.10.28(1), p. 192.
    Exclude the separate case of one member
    containing the entire test interval. *)
Lemma finite_interval_left_boundary_exists (R : realType) (I : choiceType) (F : {fset I})
    (l r : I -> R) (a b : R) :
  a<=b ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  (forall i, i \in F -> l i<=a -> b<=r i -> False) ->
  exists (L : option I) (v0 v1 : R),
    (v0<=a /\ a<=v1 /\ v1<=b) /\
    (match L with Some i=>i \in F /\ v0=l i /\ v1=r i | None=>v0=a /\ v1=a end) /\
    forall i, i \in F -> l i<=a -> a<=r i -> L=Some i.
Proof.
move=> hab hdis hnone.
case: (pselect (exists i, i \in F /\ l i<=a /\ a<=r i))=> [[i [hi [hil hir]]]|hno].
- have hrb : r i<=b.
    case: (leP (r i) b)=> // hbr; exfalso; exact: hnone i hi hil (ltW hbr).
  exists (Some i),(l i),(r i); split; first by split=> //; split.
  split; first by split=> //; split.
  move=> j hj hjl hjr; congr (Some _).
  exact: finite_disjoint_endpoint_member_unique hdis hi hj hil hir hjl hjr.
- exists None,a,a; split; first by split=> //; split.
  split; first by split.
  move=> i hi hil hir; exfalso; apply: hno; exists i; by split=> //; split.
Qed.

(** Source for [finite_interval_right_boundary_exists]:
    supporting right endpoint member or zero-cost
    point placeholder for 2.10.28(1), p. 192.
    This is the symmetric endpoint selection;
    no interval orientation is silently changed. *)
Lemma finite_interval_right_boundary_exists (R : realType) (I : choiceType) (F : {fset I})
    (l r : I -> R) (a b : R) :
  a<=b ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  (forall i, i \in F -> l i<=a -> b<=r i -> False) ->
  exists (W : option I) (w0 w1 : R),
    (a<=w0 /\ w0<=b /\ b<=w1) /\
    (match W with Some i=>i \in F /\ w0=l i /\ w1=r i | None=>w0=b /\ w1=b end) /\
    forall i, i \in F -> l i<=b -> b<=r i -> W=Some i.
Proof.
move=> hab hdis hnone.
case: (pselect (exists i, i \in F /\ l i<=b /\ b<=r i))=> [[i [hi [hil hir]]]|hno].
- have hal : a<=l i.
    case: (leP a (l i))=> // hla; exfalso; exact: hnone i hi (ltW hla) hir.
  exists (Some i),(l i),(r i); split; first by split=> //; split.
  split; first by split=> //; split.
  move=> j hj hjl hjr; congr (Some _).
  exact: finite_disjoint_endpoint_member_unique hdis hi hj hil hir hjl hjr.
- exists None,b,b; split; first by split=> //; split.
  split; first by split.
  move=> i hi hil hir; exfalso; apply: hno; exists i; by split=> //; split.
Qed.

(** Source for [finite_interval_boundary_exists]: supporting
    simultaneous boundary members for the two
    enlargement inequalities of 2.10.28(1),
    p. 192. No shrinking, nonempty family
    or nondegenerate member hypothesis is added. *)
Lemma finite_interval_boundary_exists (R : realType) (I : choiceType) (F : {fset I})
    (l r : I -> R) (a b : R) :
  a<=b ->
  (forall i j, i \in F -> j \in F -> i!=j -> r i<l j \/ r j<l i) ->
  (forall i, i \in F -> l i<=a -> b<=r i -> False) ->
  exists L W v0 v1 w0 w1, is_finite_interval_boundary F l r a b L W v0 v1 w0 w1.
Proof.
move=> hab hdis hnone.
have [L [v0 [v1 [[hva [hav hvb]] [hL hLd]]]]] := finite_interval_left_boundary_exists hab hdis hnone.
have [W [w0 [w1 [[haw [hwb hbw]] [hW hWd]]]]] := finite_interval_right_boundary_exists hab hdis hnone.
have hvw : v1<=w0.
  case: L hL hLd=> [i|] /= hL hLd; case: W hW hWd=> [j|] /= hW hWd.
  - have [hi [hv0 hv1]] := hL; have [hj [hw0 hw1]] := hW.
    have hlia : l i<=a by rewrite -hv0.
    have hbrj : b<=r j by rewrite -hw1.
    have hij : i!=j.
      apply/negP=> /eqP he; rewrite -he in hbrj; exact: hnone i hi hlia hbrj.
    case: (hdis i j hi hj hij)=> hgap.
    + rewrite hv1 hw0; exact: ltW hgap.
    + have hrja : r j<a := lt_le_trans hgap hlia.
      by have hh := le_lt_trans (le_trans hab hbrj) hrja; rewrite ltxx in hh.
  - rewrite hW.1; exact hvb.
  - rewrite hL.2; exact haw.
  - rewrite hL.2 hW.1; exact hab.
exists L,W,v0,v1,w0,w1; constructor=> //; by split=> //; split=> //; split=> //; split.
Qed.

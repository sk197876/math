(** General topology supporting the open-cover alternative of Federer
    (1969), 2.10.3, p. 172. A product neighbourhood contains a box imposing
    the same positive metric radius in every coordinate; for a finite
    coordinate domain these boxes are open. The auxiliary uniform-box filter
    proves the first assertion directly from the product topology. These are
    support lemmas, not extra claims attributed to Federer. Source context
    and finite-product context: ExteriorEndpointContinuity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import MetricClosedBalls ProductCoordinateNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_coordinate_box]: supporting uniform
    endpoint neighbourhood for the open enlargement in
    Federer 2.10.3, p. 172. No distance on the
    whole product is introduced or assumed. *)
Definition metric_coordinate_box (R : realType) (I : choiceType) (X : metricType R)
    (p : I -> X) (r : R) : set (I -> X) :=
  [set q | forall i, mdist (p i) (q i)<r].

(** Source for [metric_coordinate_box_self]: supporting
    nonempty positive-radius boxes in the finite-cover
    argument for Federer 2.10.3, p. 172. *)
Lemma metric_coordinate_box_self (R : realType) (I : choiceType) (X : metricType R)
    (p : I -> X) (r : R) : 0<r -> metric_coordinate_box p r p.
Proof. by move=> hr i; rewrite mdistxx. Qed.

(** Source for [metric_coordinate_box_mono]: supporting
    radius reduction for the endpoint neighbourhoods in
    Federer 2.10.3, p. 172. *)
Lemma metric_coordinate_box_mono (R : realType) (I : choiceType) (X : metricType R)
    (p : I -> X) (r s : R) : r<=s -> metric_coordinate_box p r `<=` metric_coordinate_box p s.
Proof. move=> hrs q hq i; exact: lt_le_trans (hq i) hrs. Qed.

(** Source for [metric_coordinate_box_triangle]: supporting
    composition of endpoint neighbourhoods for the open
    enlargement in Federer 2.10.3, p. 172. *)
Lemma metric_coordinate_box_triangle (R : realType) (I : choiceType) (X : metricType R)
    (p q z : I -> X) (r s : R) :
  metric_coordinate_box p r q -> metric_coordinate_box q s z -> metric_coordinate_box p (r+s) z.
Proof.
move=> hp hq i; exact: le_lt_trans (metric_triangle (p i) (q i) (z i)) (ltrD (hp i) (hq i)).
Qed.

(** Source for [finite_metric_coordinate_box_open]: supporting
    openness of finite endpoint boxes for the compact
    finite-cover proof of Federer 2.10.3, p. 172.
    The empty coordinate domain gives the whole product. *)
Lemma finite_metric_coordinate_box_open (R : realType) (I : finType) (X : metricType R)
    (p : I -> X) (r : R) : open (metric_coordinate_box p r).
Proof.
have ho i : open [set q : I -> X | mdist (p i) (q i)<r].
  exact (@coordinate_cylinder_open I (fun _ => X) i
    [set x | mdist (p i) x<r] (metric_open_ball_open (p i) r)).
rewrite openE=> q hq; apply: (@filter_forall (I -> X) I
  (fun i => [set z : I -> X | mdist (p i) (z i)<r]) (nbhs q) (nbhs_filter q)).
move=> i; have hi := ho i; rewrite openE in hi; exact: hi q (hq i).
Qed.

(** Source for [product_neighbourhood_coordinate_box]:
    supporting common-radius neighbourhood for the
    compact endpoint argument in Federer 2.10.3, p. 172.
    This direction also holds for infinite index domains;
    finiteness is needed only for openness of the boxes. *)
Theorem product_neighbourhood_coordinate_box (R : realType) (I : choiceType) (X : metricType R)
    (p : I -> X) (U : set (I -> X)) :
  nbhs p U -> exists r : R, 0<r /\ metric_coordinate_box p r `<=` U.
Proof.
move=> hU.
pose G := filter_from [set r : R | 0<r] (metric_coordinate_box p).
have hG : Filter G.
  apply: filter_from_filter; first by exists 1; exact: ltr01.
  move=> r s hr hs; exists (Order.min r s); first by rewrite /= lt_min hr hs.
  move=> q hq; split.
  - apply: (@metric_coordinate_box_mono R I X p (Order.min r s) r _ q hq).
    by rewrite ge_min lexx.
  - apply: (@metric_coordinate_box_mono R I X p (Order.min r s) s _ q hq).
    by rewrite ge_min lexx orbT.
have hconv : G --> p.
  apply/cvg_sup=> i V; rewrite (@nbhsE (initial_topology (fun q : I -> X => q i))).
  move=> [W [[O hO <-] hpi] hWV].
  have hn : nbhs (p i) O by rewrite openE in hO; exact: hO _ hpi.
  have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP (p i) O) hn.
  exists r=> // q hq; apply: hWV; exact: hb _ (hq i).
have [r hr hb] := hconv U hU; exists r; by split.
Qed.

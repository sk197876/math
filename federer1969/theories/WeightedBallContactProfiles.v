(** Federer (1969), 2.10.40, printed p. 200: compactness passes small
    perturbation constraints to a contact pair with a nonpositive
    directional coordinate. The scalar slack and direction profiles below
    make those closed constraints explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm
  InnerMetric InnerNormedTopology InnerCoordinateContinuity OrthonormalFamilies
  TopologicalProductMaps Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_slack]: supporting scalar
    r c-|b-a| for the contact equality in
    2.10.40, p. 200. Feasible centres have
    nonnegative slack, and contact is exactly slack zero. *)
Definition weighted_ball_slack (R : realType) n
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R)
    (p : (inner_metric_space (@euclidean_inner_productP R n))*R) :=
  p.2*c-inner_norm (@euclidean_inner_productP R n) (b-p.1).

(** Source for [weighted_ball_direction]: supporting scalar
    u dot (a-b) for the contact-separation argument
    of 2.10.40, p. 200. Translation by b
    keeps the original parameter family unchanged. *)
Definition weighted_ball_direction (R : realType) n
    (u b : inner_metric_space (@euclidean_inner_productP R n))
    (p : (inner_metric_space (@euclidean_inner_productP R n))*R) :=
  euclidean_inner_product u (p.1-b).

(** Source for [weighted_ball_slack_continuous]: supporting
    closed contact and approximate-contact constraints
    for 2.10.40, p. 200. Continuity holds
    on the whole parameter product, without a positivity
    or compactness premise. *)
Lemma weighted_ball_slack_continuous (R : realType) n
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :
  continuous (@weighted_ball_slack R n b c :
    (inner_metric_space (@euclidean_inner_productP R n))*R^o -> R^o).
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have hN : continuous (fun x : E=>(inner_norm (@euclidean_inner_productP R n) x : R^o)).
  exact: norm_continuous.
rewrite /weighted_ball_slack=> p.
apply: (@continuousB R R^o [the topologicalType of (E*R^o)%type]
  (fun q=>q.2*c) (fun q=>inner_norm (@euclidean_inner_productP R n) (b-q.1)) p).
- apply: (@continuousM R [the topologicalType of (E*R^o)%type] snd (fun _=>c) p).
  + exact: second_projection_continuous.
  + exact: cst_continuous.
- apply: (@continuous_comp [the topologicalType of (E*R^o)%type]
    [the topologicalType of E] [the topologicalType of R^o]
    (fun q=>b-q.1) (fun x=>inner_norm (@euclidean_inner_productP R n) x) p).
  + apply: (@continuousB R E [the topologicalType of (E*R^o)%type] (fun _=>b) fst p).
    * exact: cst_continuous.
    * exact: first_projection_continuous.
  + exact: hN.
Qed.

(** Source for [weighted_ball_direction_continuous]: supporting
    closed halfspace constraints in 2.10.40,
    p. 200. This uses only the proved
    continuity of inner-product coordinates. *)
Lemma weighted_ball_direction_continuous (R : realType) n
    (u b : inner_metric_space (@euclidean_inner_productP R n)) :
  continuous (@weighted_ball_direction R n u b :
    (inner_metric_space (@euclidean_inner_productP R n))*R^o -> R^o).
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have he : (@weighted_ball_direction R n u b : E*R^o -> R^o)=
    (fun p=>inner_coordinate (@euclidean_inner_productP R n) u (p.1-b)).
  apply: funext=> p; rewrite inner_coordinateE.
  exact: euclidean_inner_symmetric.
rewrite he=> p.
apply: (@continuous_comp [the topologicalType of (E*R^o)%type]
  [the topologicalType of E] [the topologicalType of R^o]
  (fun q=>q.1-b) (fun x=>inner_coordinate (@euclidean_inner_productP R n) u x) p).
- apply: (@continuousB R E [the topologicalType of (E*R^o)%type] fst (fun _=>b) p).
  + exact: first_projection_continuous.
  + exact: cst_continuous.
- exact: inner_coordinate_continuous.
Qed.

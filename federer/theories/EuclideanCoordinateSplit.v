(** Federer (1969), 2.6.5, pp. 119–120: Cartesian identifications of
    Euclidean factors, including the splitting used for the
    polynomial-zero-set induction on p. 120. We split off the first scalar
    coordinate and retain the remaining coordinates in R_n, so the induction
    uses R^n times R. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNormedTopology EuclideanCoordinateTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Splitting.
Variable R : realType.
Variable n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [euclidean_join]: supporting inverse Cartesian
    identification in Federer 2.6.5, p. 120. The scalar
    factor occupies the first coordinate. *)
Definition euclidean_join (p : E n * R) : E n.+1 :=
  @coordinate_tail_inclusion R n p.1 + @coordinate_head_inclusion R n p.2.

(** Source for [euclidean_split]: supporting Euclidean
    Cartesian identification in Federer 2.6.5, p. 120,
    with remaining coordinates first and scalar coordinate second. *)
Definition euclidean_split (x : E n.+1) : E n * R :=
  (coordinate_tail x, coordinate_head x).

(** Source for [euclidean_join_head]: supporting first
    coordinate law for the identification in Federer
    2.6.5, p. 120. *)
Lemma euclidean_join_head p : euclidean_join p ord0 = p.2.
Proof.
by rewrite /euclidean_join /coordinate_tail_inclusion /coordinate_head_inclusion !ffunE unlift_none eqxx add0r.
Qed.

(** Source for [euclidean_join_tail]: supporting remaining
    coordinate law for Federer 2.6.5, p. 120. *)
Lemma euclidean_join_tail p i : euclidean_join p (lift ord0 i) = p.1 i.
Proof.
by rewrite /euclidean_join /coordinate_tail_inclusion /coordinate_head_inclusion !ffunE liftK lift_eqF addr0.
Qed.

(** Source for [euclidean_joinK]: supporting inverse identity
    for the usual Cartesian map in Federer 2.6.5, p. 120,
    including n=0. *)
Lemma euclidean_joinK : cancel euclidean_join euclidean_split.
Proof.
move=> [u t]; rewrite /euclidean_split /coordinate_head euclidean_join_head /=.
congr (_,t); apply/ffunP=> i; by rewrite /coordinate_tail ffunE euclidean_join_tail.
Qed.

(** Source for [euclidean_splitK]: supporting other inverse
    identity for Federer 2.6.5, p. 120. *)
Lemma euclidean_splitK : cancel euclidean_split euclidean_join.
Proof.
move=> x; rewrite /euclidean_join /euclidean_split /= addrC.
exact: coordinate_decomposition.
Qed.

(** Source for [euclidean_join_continuous]: supporting
    homeomorphism property of the Euclidean identification
    used for Borel regularity in Federer 2.6.5, p. 120. *)
Lemma euclidean_join_continuous : continuous euclidean_join.
Proof.
apply: euclidean_map_continuous=> i.
case: (unliftP ord0 i)=> [j ->|->].
- have he : (fun p : E n * R => euclidean_join p (lift ord0 j)) = (fun p => p.1 j).
    exact: funext (fun p => euclidean_join_tail p j).
  rewrite he=> p.
  apply: (@continuous_comp (Topological.clone (E n * R)%type _)
    (Topological.clone (E n) _) (Topological.clone R^o _) (@fst (E n) R) (fun x => x j) p).
  + exact: first_projection_continuous.
  + exact (@euclidean_coordinate_continuous R n j p.1).
- have he : (fun p : E n * R => euclidean_join p ord0) = (fun p => p.2).
    exact: funext euclidean_join_head.
  rewrite he; exact: second_projection_continuous.
Qed.

(** Source for [euclidean_split_continuous]: supporting
    continuity of the inverse Cartesian identification
    in Federer 2.6.5, p. 120. *)
Lemma euclidean_split_continuous : continuous euclidean_split.
Proof.
apply: topological_pair_continuous.
- apply: euclidean_map_continuous=> i.
  have he : (fun x : E n.+1 => coordinate_tail x i) = (fun x => x (lift ord0 i)).
    by apply: funext=> x; rewrite /coordinate_tail ffunE.
  rewrite he; exact: euclidean_coordinate_continuous.
- exact: (@euclidean_coordinate_continuous R n.+1 ord0).
Qed.
End Splitting.

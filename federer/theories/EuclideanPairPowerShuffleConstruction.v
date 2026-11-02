(** Private coordinate regrouping witness for Federer (1969), 2.10.29, p.
    195. Recursively put the two scalar heads into one planar block and
    regroup the two tails. Both inverse maps, squared-distance preservation
    and membership laws must be proved before selecting the opaque shuffle.
    The recursion stays private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanOneCoordinate EuclideanRealPlane EuclideanCoordinateSplit EuclideanBlockCoordinates
  EuclideanMetricProduct EuclideanHeadTailGeometry EuclideanSetPowerCoordinates EuclideanSetPowers
  EuclideanCantorProduct EuclideanBlockSetPower EuclideanMeasurePowerUP EuclideanPairPowerShuffleUP
  MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [pair_power_shuffle_forward_witness]: private
    recursive coordinate permutation witnessing the
    forward regrouping in 2.10.29, p. 195. *)
Fixpoint pair_power_shuffle_forward_witness q0 : (E q0.+1*E q0.+1)%type -> E (euclidean_power_dimension 2 q0) :=
  match q0 as k return (E k.+1*E k.+1)%type -> E (euclidean_power_dimension 2 k) with
  | 0 => fun p=>euclidean_real_plane_pair (euclidean_one_project p.1) (euclidean_one_project p.2)
  | k.+1 => fun p=>euclidean_block_join
      (@pair_power_shuffle_forward_witness k (coordinate_tail p.1,coordinate_tail p.2),
        euclidean_real_plane_pair (coordinate_head p.1) (coordinate_head p.2))
  end.

(** Source for [pair_power_shuffle_backward_witness]: private
    inverse recursion for the regrouping in
    2.10.29, p. 195. It separates each
    final planar block into two scalar heads. *)
Fixpoint pair_power_shuffle_backward_witness q0 : E (euclidean_power_dimension 2 q0) -> (E q0.+1*E q0.+1)%type :=
  match q0 as k return E (euclidean_power_dimension 2 k) -> (E k.+1*E k.+1)%type with
  | 0 => fun x=>(euclidean_one_embed (euclidean_real_plane_first x),euclidean_one_embed (euclidean_real_plane_second x))
  | k.+1 => fun x=>
      let p := @euclidean_block_split R (euclidean_power_dimension 2 k) 2 x in
      let u := @pair_power_shuffle_backward_witness k p.1 in
      (euclidean_join (u.1,euclidean_real_plane_first p.2),
        euclidean_join (u.2,euclidean_real_plane_second p.2))
  end.

(** Source for [pair_power_shuffle_witness_forwardK]: supporting
    first inverse law for the private
    regrouping witness in 2.10.29, p. 195. *)
Lemma pair_power_shuffle_witness_forwardK : forall q,
  cancel (@pair_power_shuffle_forward_witness q) (@pair_power_shuffle_backward_witness q).
Proof.
elim=> [p|q ih p].
- rewrite /pair_power_shuffle_forward_witness /pair_power_shuffle_backward_witness
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) !euclidean_one_projectK.
  by case: p.
- rewrite /pair_power_shuffle_forward_witness /pair_power_shuffle_backward_witness
    euclidean_block_joinK.
  fold (@pair_power_shuffle_forward_witness q) (@pair_power_shuffle_backward_witness q).
  rewrite /= ih
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  change ((@euclidean_join R q.+1 (euclidean_split p.1),@euclidean_join R q.+1 (euclidean_split p.2))=p).
  rewrite !euclidean_splitK; by case: p.
Qed.

(** Source for [pair_power_shuffle_witness_backwardK]: supporting
    second inverse law for the private
    regrouping witness in 2.10.29, p. 195. *)
Lemma pair_power_shuffle_witness_backwardK : forall q,
  cancel (@pair_power_shuffle_backward_witness q) (@pair_power_shuffle_forward_witness q).
Proof.
have htail n (p : E n*R) : coordinate_tail (euclidean_join p)=p.1.
  have hh := congr1 fst (@euclidean_joinK R n p); exact hh.
have hhead n (p : E n*R) : coordinate_head (euclidean_join p)=p.2.
  have hh := congr1 snd (@euclidean_joinK R n p); exact hh.
elim=> [x|q ih x].
- rewrite /pair_power_shuffle_forward_witness /pair_power_shuffle_backward_witness !euclidean_one_embedK.
  exact (metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R) x).
- rewrite /pair_power_shuffle_forward_witness /pair_power_shuffle_backward_witness !htail !hhead.
  fold (@pair_power_shuffle_forward_witness q) (@pair_power_shuffle_backward_witness q).
  rewrite /= -surjective_pairing ih
    (metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R)).
  exact (@euclidean_block_splitK R (euclidean_power_dimension 2 q) 2 x).
Qed.

(** Source for [pair_power_shuffle_witness_squared_distance]: supporting
    orthogonal squared-distance law for the private
    coordinate permutation in 2.10.29, p. 195.
    The induction uses actual Euclidean block and
    head-tail Pythagorean identities. *)
Lemma pair_power_shuffle_witness_squared_distance : forall q p s,
  mdist (@pair_power_shuffle_forward_witness q p) (@pair_power_shuffle_forward_witness q s)^+2=
    mdist p.1 s.1^+2+mdist p.2 s.2^+2.
Proof.
have hpair (a b c d : real_line_metric R) :
    mdist (euclidean_real_plane_pair a b) (euclidean_real_plane_pair c d)^+2=`|a-c|^+2+`|b-d|^+2.
  by rewrite euclidean_real_plane_squared_distance
    !(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    !(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
have hone (x y : E 1) : `|euclidean_one_project x-euclidean_one_project y|=mdist x y.
  by rewrite euclidean_one_project_distance real_line_metric_distanceE.
elim=> [p s|q ih p s].
- by rewrite /pair_power_shuffle_forward_witness hpair !hone.
- rewrite /pair_power_shuffle_forward_witness
    (@euclidean_block_squared_distance R (euclidean_power_dimension 2 q) 2)
    !euclidean_block_joinK.
  fold (@pair_power_shuffle_forward_witness q).
  cbn [fst snd].
  rewrite ih hpair !(@euclidean_head_tail_squared_distance R q.+1).
  ring.
Qed.

(** Source for [pair_power_shuffle_witness_membership]: direct
    Cartesian set identification of 2.10.29,
    p. 195, for the private coordinate
    witness, uniformly over both scalar sets. *)
Lemma pair_power_shuffle_witness_membership : forall q (A B : set (real_line_metric R)) u v,
  @euclidean_block_set_power R 2 (euclidean_cantor_product A B) q
    (@pair_power_shuffle_forward_witness q (u,v)) <->
      euclidean_set_power q.+1 A u /\ euclidean_set_power q.+1 B v.
Proof.
have hpairmem (A B : set (real_line_metric R)) (x y : real_line_metric R) :
    euclidean_cantor_product A B (euclidean_real_plane_pair x y) <-> A x /\ B y.
  change ((A (euclidean_real_plane_first (euclidean_real_plane_pair x y)) /\
    B (euclidean_real_plane_second (euclidean_real_plane_pair x y))) <-> A x /\ B y).
  by rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
have hstep n (A B : set (real_line_metric R)) (p : E (euclidean_power_dimension 2 n)) (r : E 2) :
    @euclidean_block_set_power R 2 (euclidean_cantor_product A B) n.+1 (euclidean_block_join (p,r)) <->
      @euclidean_block_set_power R 2 (euclidean_cantor_product A B) n p /\ euclidean_cantor_product A B r.
  rewrite euclidean_block_set_power_successorE.
  change ((@euclidean_block_set_power R 2 (euclidean_cantor_product A B) n
    (@euclidean_block_split R (euclidean_power_dimension 2 n) 2 (euclidean_block_join (p,r))).1 /\
    euclidean_cantor_product A B (@euclidean_block_split R (euclidean_power_dimension 2 n) 2 (euclidean_block_join (p,r))).2) <->
    @euclidean_block_set_power R 2 (euclidean_cantor_product A B) n p /\ euclidean_cantor_product A B r).
  by rewrite euclidean_block_joinK.
elim=> [A B u v|q ih A B u v].
- rewrite euclidean_block_set_power_firstE /pair_power_shuffle_forward_witness hpairmem
    !euclidean_set_power_one_membership; by [].
- change (@euclidean_block_set_power R 2 (euclidean_cantor_product A B) q.+1
    (euclidean_block_join (@pair_power_shuffle_forward_witness q (coordinate_tail u,coordinate_tail v),
      euclidean_real_plane_pair (coordinate_head u) (coordinate_head v))) <->
    euclidean_set_power q.+2 A u /\ euclidean_set_power q.+2 B v).
  rewrite hstep ih hpairmem !euclidean_set_power_head_tail_membership.
  by split=> [[[/= hA hB] [ha hb]]|[[hA ha] [hB hb]]]; split; split.
Qed.

(** Source for [euclidean_pair_power_shuffle_exists]: supporting
    proved existence of an inverse, orthogonal
    coordinate regrouping realising the identification
    in 2.10.29, p. 195. *)
Theorem euclidean_pair_power_shuffle_exists q : exists D : euclidean_pair_power_shuffle_data R q, is_euclidean_pair_power_shuffle D.
Proof.
exists (@Build_euclidean_pair_power_shuffle_data R q
  (@pair_power_shuffle_forward_witness q) (@pair_power_shuffle_backward_witness q)).
constructor.
- exact (@pair_power_shuffle_witness_forwardK q).
- exact (@pair_power_shuffle_witness_backwardK q).
- exact (@pair_power_shuffle_witness_squared_distance q).
- exact (@pair_power_shuffle_witness_membership q).
Qed.
End Construction.

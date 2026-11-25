(** Federer (1969), 4.1.8, p. 361: the original
    actual-domain identification is a homeomorphism. Derive
    its inverse and continuity laws from the opaque
    coordinate specification and the already proved block
    maps in the original norm topologies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanBlockNormTopology CurrentDomain CurrentCartesianDomainMapsSealed
  IsotropyGroupTopology TopologicalProductMaps HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentCartesianDomainMapsLaws.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation N k := (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R k))).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) AB).
Local Notation PT := [the topologicalType of (AT*BT)%type].
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).

(** Source for [current_cartesian_domain_join_value]: the opaque
    actual-domain join has the original block values,
    supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_domain_join_value (z:AT*BT):
  set_val (J z)=euclidean_block_join (set_val z.1,set_val z.2).
Proof. exact:((@CartesianCurrentDomain.laws R m n A B).1 z). Qed.

(** Source for [current_cartesian_domain_split_values]: the opaque
    actual-domain split has the original first and second
    coordinates, supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_domain_split_values (w:CT):
  (set_val ((D w).1),set_val ((D w).2))=@euclidean_block_split R m n (set_val w).
Proof.
have[hFirst hSecond]:=(@CartesianCurrentDomain.laws R m n A B).2 w.
change ((set_val ((D w).1),set_val ((D w).2))=
  (@euclidean_first_block_map R m n (set_val w),@euclidean_last_block_map R m n (set_val w))).
by rewrite hFirst hSecond.
Qed.

(** Source for [current_cartesian_domain_join_split]: splitting
    the joined original factor points recovers those same
    points, supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_join_split:cancel J D.
Proof.
move=>z.
have hPair:=current_cartesian_domain_split_values (J z).
rewrite current_cartesian_domain_join_value euclidean_block_joinK in hPair.
apply:injective_projections.
- apply:val_inj;exact:(congr1 fst hPair).
- apply:val_inj;exact:(congr1 snd hPair).
Qed.

(** Source for [current_cartesian_domain_split_join]: joining
    the original split point recovers that point,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_split_join:cancel D J.
Proof.
move=>w;apply:val_inj.
have hValue:=current_cartesian_domain_join_value (D w).
by rewrite current_cartesian_domain_split_values euclidean_block_splitK in hValue.
Qed.

(** Source for [current_cartesian_domain_join_continuous]: the
    original join is continuous on the actual factor
    subspaces, supporting the product Radon transport in
    Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_join_continuous:continuous J.
Proof.
apply:(@set_type_continuous_into (N (m+n)) AB PT J).
have he:(fun z:PT=>set_val (J z))=
    (fun z:PT=>@euclidean_block_join R m n (set_val z.1,set_val z.2)).
  apply:funext=>z;exact:current_cartesian_domain_join_value.
change (continuous (fun z:PT=>set_val (J z))).
rewrite he.
have hPair:continuous (fun z:PT=>((set_val z.1:N m),(set_val z.2:N n))).
  apply:topological_pair_continuous.
  - move=>z;exact:(continuous_comp (@first_projection_continuous AT BT z)
      (@set_type_val_continuous (N m) A z.1)).
  - move=>z;exact:(continuous_comp (@second_projection_continuous AT BT z)
      (@set_type_val_continuous (N n) B z.2)).
move=>z;exact:(continuous_comp (@hPair z)
  (@euclidean_block_join_norm_continuous R m n (set_val z.1,set_val z.2))).
Qed.

(** Source for [current_cartesian_domain_split_continuous]: the
    inverse original split is continuous on the actual
    product subspace, supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_split_continuous:continuous D.
Proof.
have hRaw:continuous (fun w:CT=>(@euclidean_block_split R m n (set_val w):(N m*N n)%type)).
  move=>w;exact:(continuous_comp (@set_type_val_continuous (N (m+n)) AB w)
    (@euclidean_block_split_norm_continuous R m n (set_val w))).
have hSame:(fun w:CT=>((D w).1,(D w).2))=D.
  apply:funext=>w;by case:(D w).
rewrite -hSame;apply:topological_pair_continuous.
- apply:(@set_type_continuous_into (N m) A CT (fun w=>(D w).1)).
  have he:(fun w:CT=>set_val ((D w).1))=
      (fun w:CT=>(@euclidean_block_split R m n (set_val w)).1).
    apply:funext=>w;exact:((@CartesianCurrentDomain.laws R m n A B).2 w).1.
  change (continuous (fun w:CT=>set_val ((D w).1))).
  rewrite he=>w;exact:(continuous_comp (@hRaw w)
    (@first_projection_continuous (N m) (N n) (euclidean_block_split (set_val w)))).
- apply:(@set_type_continuous_into (N n) B CT (fun w=>(D w).2)).
  have he:(fun w:CT=>set_val ((D w).2))=
      (fun w:CT=>(@euclidean_block_split R m n (set_val w)).2).
    apply:funext=>w;exact:((@CartesianCurrentDomain.laws R m n A B).2 w).2.
  change (continuous (fun w:CT=>set_val ((D w).2))).
  rewrite he=>w;exact:(continuous_comp (@hRaw w)
    (@second_projection_continuous (N m) (N n) (euclidean_block_split (set_val w)))).
Qed.

(** Source for [current_cartesian_domain_homeomorphism]: the
    original factor product and Euclidean product domain are
    homeomorphic by their actual block maps, supporting the
    original product measure in Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_homeomorphism:is_homeomorphism_with_inverse J D.
Proof.
constructor.
- exact:current_cartesian_domain_join_continuous.
- exact:current_cartesian_domain_split_continuous.
- exact:current_cartesian_domain_join_split.
- exact:current_cartesian_domain_split_join.
Qed.
End CurrentCartesianDomainMapsLaws.

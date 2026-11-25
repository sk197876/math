(** Federer (1969), 4.1.8, p. 361: the original
    product-domain identification for the variation product measure.
    Specify the join and split on the actual factor
    subspaces by their existing Euclidean block values.
    Existence and uniqueness are proved separately below. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentCartesianDomainMapsUP.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) AB).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [is_current_cartesian_domain_maps]: the
    canonical product identification has the original coordinate
    values on the actual factor domains, supporting Federer
    4.1.8, p. 361, by 2.6.5, p. 120.
    No existence, cancellation or continuity is assumed. *)
Definition is_current_cartesian_domain_maps
    (J:(AT*BT)%type->CT) (D:CT->(AT*BT)%type):Prop:=
  (forall z,set_val (J z)=euclidean_block_join (set_val z.1,set_val z.2)) /\
  (forall w,set_val ((D w).1)=p (set_val w) /\set_val ((D w).2)=q (set_val w)).

(** Source for [current_cartesian_domain_maps_exists]: the
    original join and split exist on the actual
    factor subspaces, supporting Federer 4.1.8, p. 361.
    The earlier block inverse law verifies membership;
    these subtype constructions serve only existence. *)
Theorem current_cartesian_domain_maps_exists:
  exists J:(AT*BT)%type->CT,exists D:CT->(AT*BT)%type,
    is_current_cartesian_domain_maps J D.
Proof.
have hImage (z:AT*BT):AB (euclidean_block_join (set_val z.1,set_val z.2)).
  change (A ((@euclidean_block_split R m n
      (euclidean_block_join (set_val z.1,set_val z.2))).1) /\
    B ((@euclidean_block_split R m n
      (euclidean_block_join (set_val z.1,set_val z.2))).2)).
  rewrite euclidean_block_joinK;exact:conj (set_valP z.1) (set_valP z.2).
pose J (z:AT*BT):CT:=exist _ (euclidean_block_join (set_val z.1,set_val z.2)) (mem_set (@hImage z)).
pose D (w:CT):AT*BT:=
  (exist _ (p (set_val w)) (mem_set (set_valP w).1),
   exist _ (q (set_val w)) (mem_set (set_valP w).2)).
exists J,D;split;first by move=>z.
by move=>w;split.
Qed.

(** Source for [current_cartesian_domain_maps_unique]: the
    original coordinate laws uniquely determine both domain
    identifications, supporting the product measure transport
    in Federer 4.1.8, p. 361. *)
Theorem current_cartesian_domain_maps_unique
    (J J':(AT*BT)%type->CT) (D D':CT->(AT*BT)%type):
  is_current_cartesian_domain_maps J D->is_current_cartesian_domain_maps J' D'->
    J=J' /\D=D'.
Proof.
move=>[hJ hD] [hJ' hD'];split.
- apply:funext=>z;apply:val_inj.
  exact:(eq_trans (hJ z) (esym (hJ' z))).
- apply:funext=>w;apply:injective_projections.
  + apply:val_inj;exact:(eq_trans (hD w).1 (esym (hD' w).1)).
  + apply:val_inj;exact:(eq_trans (hD w).2 (esym (hD' w).2)).
Qed.
End CurrentCartesianDomainMapsUP.

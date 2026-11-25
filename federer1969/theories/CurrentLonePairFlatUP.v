(** Federer (1969), 4.1.18, p. 375: the
    original pair map has codomain the whole compact-index
    union F_m(U). Specify its exact inclusion equation
    before proving range, existence and surjectivity.
    Its current-valued map and the flat-union carrier
    are the independently specified opaque original objects. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentLonePairImageUP CurrentLonePairImageSealed
  FlatCurrentUnionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FlatPair.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation F:=(@flat_current_union_space R h2 n m U hU).
Local Notation inc:=(@flat_current_union_inclusion R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).

(** Source for [is_current_lone_pair_flat_map]: the
    original defining equation for q as a map
    into F_m(U), Federer 4.1.18, p. 375.
    Its range and onto theorems are separate proofs,
    not hypotheses incorporated in this specification. *)
Definition is_current_lone_pair_flat_map (Q:Hom P F):Prop:=
  forall v:P,inc (Q v)=q v.

(** Source for [current_lone_pair_flat_map_unique]:
    inclusion in the actual current space determines
    the flat-valued pair map of Federer 4.1.18,
    p. 375. No compact index is chosen. *)
Theorem current_lone_pair_flat_map_unique (Q S:Hom P F):
  is_current_lone_pair_flat_map Q->is_current_lone_pair_flat_map S->Q = S.
Proof.
move=>hQ hS;apply:hom_ext=>v.
apply:(@flat_current_union_inclusion_injective R h2 n m U hU).
exact:(eq_trans (hQ v) (esym (hS v))).
Qed.
End FlatPair.

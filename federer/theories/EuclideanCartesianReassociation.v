(** Federer (1969), 4.1.8, p. 361: the natural
    identification of three Cartesian factors preserves their
    original ordered coordinates. Reuse the dimension cast
    and coordinate-list laws of 2.6.5, p. 120;
    no replacement Cartesian carrier is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCoordinateLists EuclideanDimensionCastLinear EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_cartesian_reassociate_join]: the
    natural association of three original coordinate blocks,
    supporting product associativity in Federer 4.1.8,
    p. 361. Empty blocks are retained. *)
Lemma euclidean_cartesian_reassociate_join (R:realType) a b c
    (x:R_n R a) (y:R_n R b) (z:R_n R c):
  @euclidean_dimension_cast_map R ((a+b)+c)%N (a+(b+c))%N (esym (addnA a b c))
    (euclidean_block_join (euclidean_block_join (x,y),z))=
    euclidean_block_join (x,euclidean_block_join (y,z)).
Proof.
apply:(@euclidean_coordinate_list_injective R (a+(b+c))%N).
change (euclidean_coordinate_list (euclidean_dimension_cast (esym (addnA a b c))
  (euclidean_block_join (euclidean_block_join (x,y),z)))=
  euclidean_coordinate_list (euclidean_block_join (x,euclidean_block_join (y,z)))).
by rewrite euclidean_dimension_cast_list !euclidean_block_join_list /= catA.
Qed.

Section ThreeBlocks.
Variable R:realType.
Variables a b c:nat.
Local Notation X := (R_n R ((a+b)+c)).
Local Notation assoc := (@euclidean_dimension_cast_map R ((a+b)+c)%N (a+(b+c))%N
  (esym (addnA a b c))).
Local Notation p := (@euclidean_first_block_map R (a+b) c).
Local Notation q := (@euclidean_last_block_map R (a+b) c).
Local Notation pa := (@euclidean_first_block_map R a b).
Local Notation pb := (@euclidean_last_block_map R a b).

(** Source for [euclidean_cartesian_reassociate_blocks]: the
    exact original blocks after natural association, supporting
    Federer 4.1.8, p. 361. The proof uses
    the existing join/split inverse laws. *)
Theorem euclidean_cartesian_reassociate_blocks (x:X):
  @euclidean_block_split R a (b+c) (assoc x)=
    (pa (p x),euclidean_block_join (pb (p x),q x)).
Proof.
have hAB:=@euclidean_block_splitK R a b (p x).
change (euclidean_block_join (pa (p x),pb (p x))=p x) in hAB.
have hX:=@euclidean_block_splitK R (a+b) c x.
change (euclidean_block_join (p x,q x)=x) in hX.
have hJoin:=@euclidean_cartesian_reassociate_join R a b c (pa (p x)) (pb (p x)) (q x).
rewrite hAB hX in hJoin.
rewrite hJoin;exact:euclidean_block_joinK.
Qed.

(** Source for [euclidean_cartesian_reassociate_first]: natural
    association retains the first original factor, supporting
    Federer 4.1.8, p. 361. *)
Lemma euclidean_cartesian_reassociate_first (x:X):
  @euclidean_first_block_map R a (b+c) (assoc x)=pa (p x).
Proof. exact:(congr1 fst (euclidean_cartesian_reassociate_blocks x)). Qed.

(** Source for [euclidean_cartesian_reassociate_middle]: natural
    association retains the second original factor, supporting
    Federer 4.1.8, p. 361. *)
Lemma euclidean_cartesian_reassociate_middle (x:X):
  @euclidean_first_block_map R b c (@euclidean_last_block_map R a (b+c) (assoc x))=pb (p x).
Proof.
change ((@euclidean_block_split R b c ((@euclidean_block_split R a (b+c) (assoc x)).2)).1=pb (p x)).
by rewrite euclidean_cartesian_reassociate_blocks euclidean_block_joinK.
Qed.

(** Source for [euclidean_cartesian_reassociate_last]: natural
    association retains the third original factor, supporting
    Federer 4.1.8, p. 361. *)
Lemma euclidean_cartesian_reassociate_last (x:X):
  @euclidean_last_block_map R b c (@euclidean_last_block_map R a (b+c) (assoc x))=q x.
Proof.
change ((@euclidean_block_split R b c ((@euclidean_block_split R a (b+c) (assoc x)).2)).2=q x).
by rewrite euclidean_cartesian_reassociate_blocks euclidean_block_joinK.
Qed.

(** Source for [euclidean_cartesian_reassociate_domain]: the
    natural identification preserves exactly the original three
    factor domains, supporting Federer 4.1.8, p. 361.
    No measurability or nonemptiness premise is added. *)
Theorem euclidean_cartesian_reassociate_domain
    (A:set (R_n R a)) (B:set (R_n R b)) (C:set (R_n R c)) x:
  @euclidean_cartesian_set R (a+b) c (@euclidean_cartesian_set R a b A B) C x <->
    @euclidean_cartesian_set R a (b+c) A (@euclidean_cartesian_set R b c B C) (assoc x).
Proof.
change (((A (pa (p x)) /\B (pb (p x))) /\C (q x)) <->
  (A (@euclidean_first_block_map R a (b+c) (assoc x)) /\
    (B (@euclidean_first_block_map R b c (@euclidean_last_block_map R a (b+c) (assoc x))) /\
    C (@euclidean_last_block_map R b c (@euclidean_last_block_map R a (b+c) (assoc x)))))).
rewrite euclidean_cartesian_reassociate_first euclidean_cartesian_reassociate_middle
  euclidean_cartesian_reassociate_last.
split.
- move=>[[ha hb] hc];exact:conj ha (conj hb hc).
- move=>[ha [hb hc]];exact:conj (conj ha hb) hc.
Qed.
End ThreeBlocks.

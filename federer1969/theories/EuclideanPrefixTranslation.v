(** Federer (1969), 3.1.4, pp. 214–215: the prefix
    translations in Z and S_i, expressed in one fixed ambient space.
    These auxiliary coordinate formulas agree with the usual block
    isomorphism of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanOneCoordinate EuclideanCoordinateStaircase EuclideanSliceTranslation
  CoordinateStaircaseBlocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_prefix_inclusion]: the increment with
    prescribed first k coordinates and zero remaining coordinates in
    Federer 3.1.4, pp. 214–215. Only its coordinate laws are used below. *)
Definition euclidean_prefix_inclusion (R : realType) m k (z : R_n R k) : R_n R m :=
  [ffun i : 'I_m => (if (insub (val i) : option 'I_k) is Some j then z j else 0 : R^o)].

(** Source for [euclidean_prefix_restriction]: the first k
    coordinates in the definition of S_i in Federer 3.1.4, p. 215. *)
Definition euclidean_prefix_restriction (R : realType) m k (hk : (k<=m)%N)
    (h : R_n R m) : R_n R k := [ffun i => h (widen_ord hk i)].

(** Source for [euclidean_prefix_translation]: the point
    x+z_1 e_1+...+z_k e_k in Federer 3.1.4, p. 214. *)
Definition euclidean_prefix_translation (R : realType) m k
    (a : R_n R m) (z : R_n R k) := a+@euclidean_prefix_inclusion R m k z.

(** Source for [euclidean_prefix_inclusion_blocks]: supporting
    agreement with the first block embedding in the Fubini estimate,
    Federer 3.1.4, p. 215. Empty prefix blocks are included. *)
Lemma euclidean_prefix_inclusion_blocks (R : realType) k l (z : R_n R k) :
  @euclidean_prefix_inclusion R (k+l) k z=@euclidean_block_join R k l (z,0).
Proof.
apply: euclidean_block_vectors_ext.
- move=> i; rewrite /euclidean_prefix_inclusion ffunE euclidean_block_join_left.
  change ((if (insub (val i) : option 'I_k) is Some j then z j else 0)=z i).
  by rewrite valK.
- move=> i; rewrite /euclidean_prefix_inclusion ffunE euclidean_block_join_right ffunE.
  have hn : ((k+val i)<k)%N=false by rewrite ltnNge leq_addr.
  by rewrite /= (@insubF nat (fun j=>(j<k)%N) _ (k+val i)%N hn).
Qed.

(** Source for [euclidean_prefix_translation_blocks]: the
    prefix translation of Federer 3.1.4, p. 215, is the
    translated coordinate slice used in 3.1.3(4), p. 213. *)
Lemma euclidean_prefix_translation_blocks (R : realType) k l
    (a : R_n R (k+l)) (z : R_n R k) :
  @euclidean_prefix_translation R (k+l) k a z=
    @euclidean_slice_translation R k l a z.
Proof.
have h := @euclidean_slice_translation_prefix R k l a
  (@euclidean_block_join R k l (z,0)).
rewrite euclidean_block_joinK coordinate_prefix_block_join in h.
by rewrite /euclidean_prefix_translation euclidean_prefix_inclusion_blocks -h.
Qed.

(** Source for [euclidean_prefix_restriction_blocks]: the
    first-block projection in Federer 3.1.4, p. 215. *)
Lemma euclidean_prefix_restriction_blocks (R : realType) k l
    (hk : (k<=k+l)%N) (h : R_n R (k+l)) :
  euclidean_prefix_restriction hk h=(@euclidean_block_split R k l h).1.
Proof.
apply/ffunP=> i; rewrite /euclidean_prefix_restriction /euclidean_block_split /= !ffunE.
congr (h _); exact: val_inj.
Qed.

(** Source for [euclidean_prefix_restriction_inclusion]: extracting
    the embedded coordinates does not change them, supporting the
    coordinate identifications in Federer 3.1.4, p. 215. *)
Lemma euclidean_prefix_restriction_inclusion (R : realType) m k
    (hk : (k<=m)%N) (z : R_n R k) :
  euclidean_prefix_restriction hk (@euclidean_prefix_inclusion R m k z)=z.
Proof.
apply/ffunP=> i; rewrite /euclidean_prefix_restriction ffunE
  /euclidean_prefix_inclusion ffunE.
change ((if (insub (val i) : option 'I_k) is Some j then z j else 0)=z i).
by rewrite valK.
Qed.

(** Source for [euclidean_prefix_inclusion_restriction]: the
    first k retained coordinates in Federer 3.1.4, p. 215,
    agree with the prefix in the coordinate telescope. *)
Lemma euclidean_prefix_inclusion_restriction (R : realType) m k
    (hk : (k<=m)%N) (h : R_n R m) :
  @euclidean_prefix_inclusion R m k (euclidean_prefix_restriction hk h)=
    coordinate_prefix h k.
Proof.
apply/ffunP=> i; rewrite /euclidean_prefix_inclusion /coordinate_prefix !ffunE.
case: insubP=> [j hj hji|hj].
- rewrite hj /euclidean_prefix_restriction ffunE.
  congr (h _); apply: val_inj; exact hji.
- by rewrite (negPf hj).
Qed.

(** Source for [euclidean_prefix_translation_step]: the next
    coordinate in the path defining S_i in Federer 3.1.4, p. 215,
    adds precisely t e_i. This identity justifies the scalar section. *)
Lemma euclidean_prefix_translation_step (R : realType) m (i : 'I_m)
    (a : R_n R m) (u : R_n R i)
    (t : inner_metric_space (@euclidean_inner_productP R 1)) :
  @euclidean_prefix_translation R m (i+1) a (@euclidean_block_join R i 1 (u,t))=
    @euclidean_prefix_translation R m i a u+
      euclidean_one_project t*:(@coordinate_basis R m i).
Proof.
rewrite /euclidean_prefix_translation -addrA; congr (a+_).
apply/ffunP=> j; rewrite /euclidean_prefix_inclusion /coordinate_basis !ffunE.
change ((if (insub (val j) : option 'I_(i+1)) is Some q
         then @euclidean_block_join R i 1 (u,t) q else 0)=
    (if (insub (val j) : option 'I_i) is Some q then u q else 0)+
      euclidean_one_project t*(if j==i then 1 else 0)).
case: (eqVneq j i)=> [->|hji].
- have h1 : (insub (val i) : option 'I_(i+1))=
      Some (rshift i (ord0 : 'I_1)).
    have hv : val (rshift i (ord0 : 'I_1))=val i by rewrite /= addn0.
    rewrite -hv; exact: valK.
  have h0 : (insub (val i) : option 'I_i)=None.
    apply: insubF; exact: ltnn.
  by rewrite h1 h0 /= euclidean_block_join_right mulr1 add0r.
- rewrite mulr0 addr0.
  case: (ltnP j i)=> [hlt|hle].
  + have h1 : (insub (val j) : option 'I_(i+1))=
        Some (lshift 1 (Ordinal hlt)).
      have hv : val (lshift 1 (Ordinal hlt))=val j by [].
      rewrite -hv; exact: valK.
    have h0 : (insub (val j) : option 'I_i)=Some (Ordinal hlt).
      exact: (valK (Ordinal hlt)).
    by rewrite h1 h0 /= euclidean_block_join_left.
  + have hn0 : (j<i)%N=false by rewrite ltnNge hle.
    have hn1 : (j<i+1)%N=false.
      by rewrite addn1 ltnS leq_eqVlt val_eqE (negPf hji) /= hn0.
    by rewrite (@insubF nat (fun q=>(q<i)%N) _ (val j) hn0)
      (@insubF nat (fun q=>(q<i+1)%N) _ (val j) hn1).
Qed.

(** Source for [euclidean_prefix_restriction_step]: the first i
    coordinates and coordinate i+1 form the prefix/scalar pair
    in the Fubini estimate of Federer 3.1.4, p. 215. *)
Lemma euclidean_prefix_restriction_step (R : realType) m (i : 'I_m)
    (hi : (i<=m)%N) (hj : (i+1<=m)%N) (h : R_n R m) :
  @euclidean_block_split R i 1 (euclidean_prefix_restriction hj h)=
    (euclidean_prefix_restriction hi h,euclidean_one_embed (h i)).
Proof.
rewrite /euclidean_block_split; congr (_, _).
- apply/ffunP=> j; rewrite ffunE /euclidean_prefix_restriction !ffunE.
  congr (h _); exact: val_inj.
- apply/ffunP=> j; rewrite ffunE /euclidean_prefix_restriction
    /euclidean_one_embed !ffunE (ord1 j).
  congr (h _); apply: val_inj; by rewrite /= addn0.
Qed.

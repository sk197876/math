(** Federer (1969), 3.2.48, p. 284: actual orthonormal
    coordinates on the Cartesian inner space used for Psi.
    This supporting identification uses the linear blocks of
    2.6.5, p. 120, and the independent chart laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP ProductInner ProductInnerNormBounds ProductInnerDifferential HilbertFormCompactness
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  EuclideanCartesianLinear FiniteInnerChartUP FiniteInnerCartesianGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_inner_cartesian_direct]: supporting linear
    product coordinates for 3.2.48, p. 284. This is
    the pair of the two original chart parametrizations. *)
Definition finite_inner_cartesian_direct (R:realType) (V W:lmodType R) n v
    (e:Hom (R_n R n) V) (f:Hom (R_n R v) W):=
  product_pair_hom (hom_comp e (@euclidean_first_block_map R n v))
    (hom_comp f (@euclidean_last_block_map R n v)).

(** Source for [finite_inner_cartesian_inverse]: supporting inverse
    product coordinates for 3.2.48, p. 284. The two
    original inverse charts are joined by the actual linear
    block identification of 2.6.5, p. 120. *)
Definition finite_inner_cartesian_inverse (R:realType) (V W:lmodType R) n v
    (p:Hom V (R_n R n)) (q:Hom W (R_n R v)):=
  hom_comp (@euclidean_first_injection_map R n v)
    (hom_comp p (@product_first_projection_hom R V W))+
  hom_comp (@euclidean_last_injection_map R n v)
    (hom_comp q (@product_second_projection_hom R V W)).

(** Source for [finite_inner_cartesian_directE]: supporting exact
    coordinate values in 3.2.48, p. 284. The actual
    map agrees with the already defined Cartesian parametrization. *)
Lemma finite_inner_cartesian_directE (R:realType) (V W:lmodType R) n v
    (e:Hom (R_n R n) V) (f:Hom (R_n R v) W) z:
  finite_inner_cartesian_direct e f z=finite_inner_cartesian_parametrization e f z.
Proof.
by rewrite /finite_inner_cartesian_direct product_pair_homE !hom_compE.
Qed.

(** Source for [finite_inner_cartesian_inverseE]: supporting
    inverse values in 3.2.48, p. 284, without
    replacing either factor by a separately chosen chart. *)
Lemma finite_inner_cartesian_inverseE (R:realType) (V W:lmodType R) n v
    (p:Hom V (R_n R n)) (q:Hom W (R_n R v)) z:
  finite_inner_cartesian_inverse p q z=euclidean_block_join (p z.1,q z.2).
Proof.
rewrite /finite_inner_cartesian_inverse hom_addE !hom_compE.
exact (esym (euclidean_block_join_sum (p z.1) (q z.2))).
Qed.

(** Source for [finite_inner_cartesian_chart]: the original
    Cartesian inner space has the stated isometric coordinates,
    supporting the coarea application in 3.2.48, p. 284.
    Both inverse laws and inner-product normalization are proved
    from the factor laws; zero coordinate blocks remain. *)
Theorem finite_inner_cartesian_chart (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  is_finite_inner_chart (product_inner hB hC)
    (finite_inner_cartesian_direct e f) (finite_inner_cartesian_inverse p q).
Proof.
move=>hV hW; constructor.
- move=>z; rewrite finite_inner_cartesian_directE finite_inner_cartesian_inverseE
    /finite_inner_cartesian_parametrization /=
    (finite_inner_chart_left_inverse hV) (finite_inner_chart_left_inverse hW).
  exact:euclidean_block_splitK.
- move=>z; rewrite finite_inner_cartesian_inverseE finite_inner_cartesian_directE
    /finite_inner_cartesian_parametrization euclidean_block_joinK /=
    (finite_inner_chart_right_inverse hV) (finite_inner_chart_right_inverse hW).
  exact (esym (surjective_pairing z)).
- move=>x y; rewrite !finite_inner_cartesian_directE
    /finite_inner_cartesian_parametrization product_innerE
    (finite_inner_chart_product hV) (finite_inner_chart_product hW).
  have h:=@euclidean_block_join_inner R n v (euclidean_block_split x) (euclidean_block_split y).
  by rewrite !euclidean_block_splitK in h; exact (esym h).
Qed.

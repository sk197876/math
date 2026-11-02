(** Federer (1969), 3.2.10, p. 248: supporting translation
    between the initial/complementary coordinate volumes and
    the Cartesian blocks in the displayed diagram. This
    changes only indices, retaining the existing exterior maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps CoordinateProjection InitialIndices
  TopComplements InitialComplementSequence ExteriorGrading ExteriorHomogeneousProducts
  FiniteExteriorPowers ExteriorOperatorEstimate EuclideanCoordinateVolumes
  AlternatingCoordinates AlternatingDual CovectorProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_first_block_coordinate_projection]:
    the first projection q in Federer 3.2.10, p. 248,
    is the initial coordinate projection of 1.7.4, p. 31. *)
Lemma euclidean_first_block_coordinate_projection (R:realType) n k
    (x:R_n R (n+k)):
  @euclidean_first_block R n k x=
    coordinate_projection (Lambda_initial (leq_addr k n)) x.
Proof.
apply/ffunP=>i; rewrite coordinate_projectionE /Lambda_initial /initial_tuple tnth_mktuple
  /euclidean_first_block ffunE.
congr (x _); apply:val_inj; by [].
Qed.

(** Source for [euclidean_last_injection_basis]: supporting
    complementary basis in Federer 3.2.10, p. 248:
    inclusion of the last block preserves its ordered basis. *)
Lemma euclidean_last_injection_basis (R:realType) n k (i:'I_k):
  @euclidean_last_injection R n k (@coordinate_basis R k i)=
    @coordinate_basis R (n+k) (rshift n i).
Proof.
apply/ffunP=>t; case:(split_ordP t)=>[l ->|r ->].
- by rewrite /euclidean_last_injection euclidean_block_join_left
    /coordinate_basis !ffunE eq_lrshift.
- by rewrite /euclidean_last_injection euclidean_block_join_right
    /coordinate_basis !ffunE (inj_eq (@rshift_inj n k)).
Qed.

(** Source for [euclidean_last_block_top_volume]: the
    complementary top product in the diagram of Federer
    3.2.10, p. 248. The explicit degree cast is only
    (n+k)-n=k; the product and its orientation are unchanged. *)
Lemma euclidean_last_block_top_volume (R:realType) n k:
  exterior_reindex (addKn n k)
    (e_lambda (@coordinate_basis R (n+k))
      (val (top_complement (Lambda_initial (leq_addr k n)))))=
  exterior_power_map (hom_as_linear (@euclidean_last_injection_map R n k)) k
    (e_lambda (@coordinate_basis R k) (ord_tuple k)).
Proof.
rewrite exterior_map_indexed_product.
apply:val_inj.
change (component_val (exterior_reindex (addKn n k)
  (e_lambda (@coordinate_basis R (n+k))
    (val (top_complement (Lambda_initial (leq_addr k n))))))=
  component_val (e_lambda (fun i=>@euclidean_last_injection R n k (@coordinate_basis R k i))
    (ord_tuple k))).
rewrite exterior_reindexE !e_lambdaE
  initial_complement_sequence val_ord_tuple -map_comp.
congr (exterior_word _); apply:eq_map=>i.
exact:Logic.eq_sym (euclidean_last_injection_basis R n i).
Qed.

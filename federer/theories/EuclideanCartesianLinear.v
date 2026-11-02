(** Federer (1969), 3.2.23, p. 260: the top Jacobian
    of the componentwise differential is the product of its two
    top Jacobians. This uses the norm of a top exterior map
    on a unit source word, 1.7.6, pp. 33–34. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps CoordinateProjection EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps EuclideanBlockVolumes
  EuclideanLinearJacobian EuclideanSeparatedExteriorNorm EuclideanCartesianMap
  ExteriorNorm ExteriorGrading ExteriorMaps ExteriorOperatorEstimate TopExteriorNorm
  FiniteExteriorPowers ConcatenatedFamilies OrthonormalFamilies TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_first_injection_basis]: supporting first
    coordinate basis identity for the product Jacobian in Federer
    3.2.23, p. 260. The last-block counterpart is already proved
    for 3.2.10, p. 248. *)
Lemma euclidean_first_injection_basis (R:realType) m mu (i:'I_m):
  @euclidean_first_injection R m mu (@coordinate_basis R m i)=
    @coordinate_basis R (m+mu) (lshift mu i).
Proof.
apply/ffunP=>t; case:(split_ordP t)=>[l ->|r ->].
- by rewrite /euclidean_first_injection euclidean_block_join_left
    /coordinate_basis !ffunE (inj_eq (@lshift_inj m mu)).
- by rewrite /euclidean_first_injection euclidean_block_join_right
    /coordinate_basis !ffunE eq_rlshift.
Qed.

(** Source for [euclidean_cartesian_linear]: the componentwise
    differential Df times Dg in the displayed area calculation
    of Federer 3.2.23, p. 260. It is specified using the
    already linear coordinate inclusions and projections. *)
Definition euclidean_cartesian_linear (R:realType) m mu n v
    (A:Hom (R_n R m) (R_n R n)) (B:Hom (R_n R mu) (R_n R v)):
    Hom (R_n R (m+mu)) (R_n R (n+v)):=
  hom_comp (@euclidean_first_injection_map R n v)
    (hom_comp A (@euclidean_first_block_map R m mu))+
  hom_comp (@euclidean_last_injection_map R n v)
    (hom_comp B (@euclidean_last_block_map R m mu)).

(** Source for [euclidean_block_join_sum]: supporting decomposition
    into the two coordinate inclusions in Federer 3.2.23, p. 260,
    using the linear block identification of 2.6.5, p. 120. *)
Lemma euclidean_block_join_sum (R:realType) n v (x:R_n R n) (y:R_n R v):
  euclidean_block_join (x,y)=
    @euclidean_first_injection R n v x+@euclidean_last_injection R n v y.
Proof.
have h:=@EuclideanBlockLinear.euclidean_block_join_linear R n v 1 (x,0) (0,y).
rewrite !scale1r in h.
have he:(x,0)+(0,y)=(x,y).
  change ((x+0,0+y)=(x,y)); by rewrite addr0 add0r.
by rewrite he in h.
Qed.

(** Source for [euclidean_cartesian_linearE]: supporting exact
    evaluation of Df times Dg in Federer 3.2.23, p. 260.
    In particular the linear object agrees with the actual product map. *)
Lemma euclidean_cartesian_linearE (R:realType) m mu n v
    (A:Hom (R_n R m) (R_n R n)) (B:Hom (R_n R mu) (R_n R v)) p:
  euclidean_cartesian_linear A B p=euclidean_cartesian_map A B p.
Proof.
rewrite /euclidean_cartesian_linear hom_addE !hom_compE /euclidean_cartesian_map.
symmetry; exact:euclidean_block_join_sum.
Qed.

(** Source for [euclidean_linear_jacobian_top_word]: supporting
    evaluation in Federer 3.2.23, p. 260, of the source-top
    Jacobian on its unit coordinate word, by 1.7.6, p. 34.
    This retains deficient rank and dimension zero. *)
Lemma euclidean_linear_jacobian_top_word (R:realType) m n
    (A:Hom (R_n R m) (R_n R n)):
  euclidean_linear_jacobian m A=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (e_lambda (fun i=>A (@coordinate_basis R m i)) (ord_tuple m)).
Proof.
have ho:orthonormal_family (@euclidean_inner_product R m) (@coordinate_basis R m).
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hUnit:=orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) ho.
have h:=@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear A)
  (e_lambda (@coordinate_basis R m) (ord_tuple m)) hUnit.
by rewrite exterior_map_indexed_product in h.
Qed.

(** Source for [euclidean_cartesian_linear_jacobian]: the exact
    product Jacobian in the middle equality of Federer 3.2.23,
    p. 260: J_(m+mu)(Df times Dg)=J_m(Df) J_mu(Dg).
    No injectivity or rank hypothesis is needed for this algebraic law. *)
Theorem euclidean_cartesian_linear_jacobian (R:realType) m mu n v
    (A:Hom (R_n R m) (R_n R n)) (B:Hom (R_n R mu) (R_n R v)):
  euclidean_linear_jacobian (m+mu) (euclidean_cartesian_linear A B)=
    euclidean_linear_jacobian m A*euclidean_linear_jacobian mu B.
Proof.
have hFamily:(fun i=>euclidean_cartesian_linear A B (@coordinate_basis R (m+mu) i))=
    concatenate_family
      (fun i=>@euclidean_first_injection R n v (A (@coordinate_basis R m i)))
      (fun j=>@euclidean_last_injection R n v (B (@coordinate_basis R mu j))).
  apply:boolp.funext=>i; case:(split_ordP i)=>[j ->|j ->].
  - rewrite concatenate_family_l -euclidean_first_injection_basis euclidean_cartesian_linearE
      /euclidean_cartesian_map /euclidean_first_injection euclidean_block_joinK /=.
    by rewrite (lin0 (hom_linear B)).
  - rewrite concatenate_family_r -euclidean_last_injection_basis euclidean_cartesian_linearE
      /euclidean_cartesian_map /euclidean_last_injection euclidean_block_joinK /=.
    by rewrite (lin0 (hom_linear A)).
rewrite !euclidean_linear_jacobian_top_word hFamily.
exact:euclidean_separated_exterior_norm.
Qed.

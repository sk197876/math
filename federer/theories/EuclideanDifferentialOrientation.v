(** Federer (1969), 3.2.25, p. 261: the nonzero
    source-top differential word and its normalized simple unit
    vector. Algebraic associated-space equality follows from 1.6.1;
    no orientation, frame or differential is assumed to exist. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import ModuleQuotient Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  CoordinateProjection EuclideanCoordinateTopology InnerNorm InnerMetric InnerExteriorPositivity
  ExteriorGrading ExteriorNorm FiniteExteriorPowers AssociatedSubspace SimpleElementary SimpleProducts FiniteSpans
  EuclideanLinearJacobian EuclideanCartesianLinear InnerUnitNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_differential_top_word]: S in
    the displayed construction of 3.2.25, p. 261,
    with the standard unit top word as eta. This is
    the existing induced exterior map evaluated on eta. *)
Definition euclidean_differential_top_word (R:realType) m n (D:Hom (R_n R m) (R_n R n)):
    exterior_power (R_n R n) m:=
  e_lambda (fun i=>D (@coordinate_basis R m i)) (ord_tuple m).

(** Source for [euclidean_differential_top_word_nonzero]: the
    nonzero S needed to divide by its norm in 3.2.25,
    p. 261. Injectivity of the actual chart differential
    implies positivity of its top-source Jacobian by 1.7.6. *)
Lemma euclidean_differential_top_word_nonzero (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  injective D ->euclidean_differential_top_word D!=0.
Proof.
move=>hInjective.
have hPositive:=(euclidean_linear_jacobian_top_positive D).2 hInjective.
rewrite euclidean_linear_jacobian_top_word in hPositive.
apply/eqP=>hZero.
change (is_true (0<exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
  (euclidean_differential_top_word D))) in hPositive.
by rewrite hZero exterior_norm_zero ltxx in hPositive.
Qed.

(** Source for [euclidean_differential_top_word_associated]: the
    associated vector subspace of S is exactly the image
    of D, supporting the last clause of 3.2.25, p. 261.
    The factors form a nonzero simple product; 1.6.1,
    p. 24, identifies its associated space with their span. *)
Lemma euclidean_differential_top_word_associated (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  injective D ->[set v|FedererSimple.T (euclidean_differential_top_word D) v]=range D.
Proof.
move=>hInjective.
have hNonzero:=euclidean_differential_top_word_nonzero hInjective.
have hFactors:=@product_associated_space R (euclidean_two_nonzero R) (R_n R n)
  m (fun i=>D (@coordinate_basis R m i)) hNonzero.
have hExpansion x:D x=\sum_i x i*:D (@coordinate_basis R m i).
  rewrite -{1}(euclidean_coordinate_expansion x) linear_sum.
  apply:eq_bigr=>i _; by rewrite linearZ.
apply/seteqP; split=>v.
- move=>hAssociated; have [c hc]:=(hFactors v).1 hAssociated.
  exists (\sum_i c i*: (@coordinate_basis R m i)); first exact Logic.I.
  rewrite linear_sum; apply:(eq_trans _ (esym hc)).
  apply:eq_bigr=>i _; by rewrite linearZ.
- move=>[x _ hDx]; apply:(hFactors v).2; exists (fun i=>x i).
  exact:(eq_trans (esym hDx) (hExpansion x)).
Qed.

(** Source for [euclidean_differential_orientation_unit_simple]: the
    simple unit range of T=S divided by its norm in
    3.2.25, p. 261. Positive degrees use 1.6.1
    scalar invariance; degree zero retains the literal empty
    product, whose normalization is the unit itself. *)
Theorem euclidean_differential_orientation_unit_simple (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  injective D ->
  let hE:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  simple (inner_unit_normalization hE (euclidean_differential_top_word D)) /\
  inner_norm hE (inner_unit_normalization hE (euclidean_differential_top_word D))= 1.
Proof.
case:m D=>[|m] D hInjective hE.
- have hUnit:inner_norm hE (euclidean_differential_top_word D)= 1.
    change (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (euclidean_differential_top_word D)= 1).
    by rewrite /euclidean_differential_top_word -euclidean_linear_jacobian_top_word euclidean_linear_jacobian_zero_degree.
  rewrite /inner_unit_normalization hUnit invr1 scale1r; split; first exact:product_simple.
  exact hUnit.
- have hPositive:0<inner_norm hE (euclidean_differential_top_word D).
    change (is_true (0<exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (euclidean_differential_top_word D))).
    rewrite /euclidean_differential_top_word -euclidean_linear_jacobian_top_word.
    exact:(euclidean_linear_jacobian_top_positive D).2 hInjective.
  split; last exact:inner_unit_normalization_norm hPositive.
  apply:simple_scale; first exact:ltn0Sn.
  exact:product_simple.
Qed.

(** Source for [euclidean_differential_orientation_associated]: normalizing
    the nonzero S leaves its associated space unchanged, as
    required by 3.2.25, p. 261. The exact result is
    the image of D in all natural dimensions. *)
Lemma euclidean_differential_orientation_associated (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  injective D ->
  let hE:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  [set v|FedererSimple.T (inner_unit_normalization hE (euclidean_differential_top_word D)) v]=range D.
Proof.
move=>hInjective hE.
have hPositive:0<inner_norm hE (euclidean_differential_top_word D).
  change (is_true (0<exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (euclidean_differential_top_word D))).
  rewrite /euclidean_differential_top_word -euclidean_linear_jacobian_top_word.
  exact:(euclidean_linear_jacobian_top_positive D).2 hInjective.
have hScalar:(inner_norm hE (euclidean_differential_top_word D))^-1!=0.
  by rewrite invr_eq0 (gt_eqF hPositive).
have hSet:[set v|FedererSimple.T (inner_unit_normalization hE (euclidean_differential_top_word D)) v]=
    [set v|FedererSimple.T (euclidean_differential_top_word D) v].
  have hScale v:=@associated_scale_nonzero R (R_n R n) m (euclidean_differential_top_word D)
    (inner_norm hE (euclidean_differential_top_word D))^-1 hScalar v.
  apply/seteqP; split=>v; [exact:(hScale v).1|exact:(hScale v).2].
rewrite hSet; exact:euclidean_differential_top_word_associated hInjective.
Qed.

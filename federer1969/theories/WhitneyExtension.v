(** Federer (1969), 3.1.14, pp. 225–227: Whitney's extension
    theorem. For a closed subset A of R^m and polynomial functions
    P_a of degree at most k whose modulus rho(C,delta) tends to zero
    as delta tends to zero for each compact subset C of A, there is
    a map g of class k on R^m with D^i g(a)=D^i P_a(a) for i<=k
    and a in A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormClassOneUP NormHigherDifferentialUP NormClassHigherUP NormClassHigherFields
  NormHigherDifferentialConstant NormHigherSymmetricFormUP
  InnerNearestUP UniformFunctionNormUP PartitionDerivativeBoundsUP PartitionDerivativeBoundsLaws
  EuclideanPartitionBallCoverUP EuclideanPartitionFamilyUP EuclideanSmoothPartition
  WhitneyModulusUP WhitneyNearestCenters WhitneyExtensionFunction
  WhitneyFormBridge WhitneyExtensionInduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WhitneyExtension.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable A : set X.
Variable P : X->PolynomialFunction (R_n R m) Y.

(** Source for [federer_3_1_14]:
    Whitney's extension theorem, Federer 3.1.14, p. 225.
    The higher differentials of g are taken in the given
    continuous multilinear spaces; the scalar spaces of
    the partition of unity are the sealed ones. The empty
    set A is extended by the zero map. *)
Theorem federer_3_1_14 :
  is_whitney_jet_family NY k P A ->
  exists g : X->Y,
    norm_class_higher N NY ev ZN (fun _=>True) g k /\
    forall a, A a -> forall i, (i<=k)%N ->
      is_norm_higher_differential_form N ev ZN (fun _=>True) g i a
        (polynomial_taylor_coefficient (P a) i a).
Proof.
move=>[hA [hdeg hmodulus]].
case: (pselect (A !=set0))=>[hne|hempty]; last first.
- have hA0 : forall a, ~ A a by move=>a ha; apply: hempty; exists a.
  exists (fun _=>0); split.
  + exact: (norm_class_infinity_constant hN hNY hZ (@whitney_whole_space_interior R m) 0 k).
  + by move=>a ha; exfalso; exact: (hA0 a ha).
- have [xi hxi] := choice (whitney_nearest_point_exists hA hne).
  pose hNs := @scalar_absolute_value_norm R.
  have hW : forall i, is_continuous_multilinear_space N (fun t : R^o=>`|t|)
      (@ContinuousMultilinear.evaluation R i _ _ _ _ hN hNs)
      (@ContinuousMultilinear.norm R i _ _ _ _ hN hNs).
    by move=>i; exact: (ContinuousMultilinear.laws i hN hNs).
  have [Dmu [G [V [_ [hG [hGV hpart]]]]]] := federer_smooth_partition_exists hW.
  have ho : forall T, [set (~` A : set X)] T -> open T by move=>T ->; exact: closed_openC.
  have [S [sigma [v [hS [hfamily [_ hv]]]]]] := hpart [set (~` A : set X)] ho.
  have hV0 : forall i, 0<=V i.
    apply: (partition_derivative_bounds_nonnegative (exprn_ge0 _ (ler0n _ _)) _ hGV)=>i.
    exact: (uniform_function_norm_nonnegative (hG i)).
  have [DP [hDP hDPd]] := whitney_polynomial_fields_exist hNY hZ.
  have [DU [hDU hDUc]] := norm_class_higher_fields hN hNY hZ
    (whitney_extension_class_off hNY hZ hW P xi hfamily hA k).
  exists (whitney_extension P xi hfamily); split.
  + exact: (whitney_extension_class_higher hNY hZ hW hA hne hdeg hxi hS hV0 hv hDP hDPd
      hmodulus hDU hDUc).
  + move=>a ha i hi.
    exact: (whitney_extension_boundary_forms hNY hZ hW hA hne hdeg hxi hS hV0 hv hDP hDPd
      hmodulus hDU ha hi).
Qed.
End WhitneyExtension.

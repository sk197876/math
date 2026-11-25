(** Federer (1969), 4.1.18, p. 377: the
    original compactly carried kernel pair on U
    has zero q-image after literal ambient
    zero extension. The support stays inside
    U, so exact open restriction detects zero. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentSupportGeometry CurrentSupportLinearUnion
  CurrentBoundary CurrentBoundarySupport CurrentOpenRestriction
  CurrentOpenRestrictionBoundary CurrentSupportRestrictionZero
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableMultivectorAmbientAgreement
  CompactSummableCurrentZeroExtension CompactSummableFullConvolutionNormal
  CurrentLonePairImageUP CurrentLonePairImageSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AmbientKernel.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation FT := (current_domain R n Full).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation PF := (@current_lone_pair_space R h2 n m Full hFull).
Local Notation valueF d :=
  (@compact_summable_multivector_value R h2 n d Full hFull).
Local Notation raw d := (@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation AF d := (@compact_summable_multivector_current R h2 n d Full hFull).
Local Notation supportF d := (@current_support R h2 n Full hFull d).
Local Notation restriction d := (@current_open_restriction R h2 n d U Full hU hFull
  (fun _ _ => Logic.I)).

(** Source for [current_lone_pair_ambient_kernel]:
    original q(v)=0 implies q(v_full)=0 for
    the literal full-domain zero extensions in
    Federer 4.1.18, p. 377.
    The support condition is proved from
    actual Omega compact carriers, rather than
    assumed for the pair's boundary. *)
Theorem current_lone_pair_ambient_kernel (v : P) (w : PF) :
  valueF m w.1=(fun x : FT => raw m v.1 (set_val x)) ->
  valueF m.+1 w.2=(fun x : FT => raw m.+1 v.2 (set_val x)) ->
  @CurrentLonePair.map R h2 n m U hU v=0 ->
  @CurrentLonePair.map R h2 n m Full hFull w=0.
Proof.
move=> hFirst hSecond hZero.
have hSupportFirst : supportF m (AF m w.1) `<=` U.
  have h := @compact_summable_full_current_support R h2 n m w.1.
  rewrite (@compact_summable_multivector_full_support_agreement R h2 n m U hU
    v.1 w.1 hFirst) in h.
  exact: (subset_trans h
    (@compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1).2.1).
have hSupportSecond : supportF m.+1 (AF m.+1 w.2) `<=` U.
  have h := @compact_summable_full_current_support R h2 n m.+1 w.2.
  rewrite (@compact_summable_multivector_full_support_agreement R h2 n m.+1 U hU
    v.2 w.2 hSecond) in h.
  exact: (subset_trans h
    (@compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2).2.1).
apply: (@current_support_neighbourhood_restriction_zero R h2 n m U Full
  hU hFull (fun _ _ => Logic.I)).
- move=> x hx.
  rewrite (@CurrentLonePair.laws R h2 n m Full hFull w) in hx.
  have hUnion := @current_support_linear_union R h2 n m Full hFull 1
    (AF m w.1) (@current_boundary R h2 n m Full hFull (AF m.+1 w.2)).
  rewrite scale1r in hUnion.
  have [hFirstPoint|hSecondPoint] := hUnion x hx.
  + exact: (@hSupportFirst x hFirstPoint).
  + apply: (@hSupportSecond x).
    exact: (@current_boundary_support_subset R h2 n m Full hFull
      (AF m.+1 w.2) x hSecondPoint).
- rewrite (@CurrentLonePair.laws R h2 n m Full hFull w)
    (linD (hom_linear (restriction m)))
    (@current_open_restriction_boundary R h2 n m U Full hU hFull
      (fun _ _ => Logic.I) (AF m.+1 w.2))
    -(@compact_summable_current_zero_extension R h2 n m U hU v.1 w.1 hFirst)
    -(@compact_summable_current_zero_extension R h2 n m.+1 U hU v.2 w.2 hSecond).
  by rewrite -(@CurrentLonePair.laws R h2 n m U hU v).
Qed.
End AmbientKernel.

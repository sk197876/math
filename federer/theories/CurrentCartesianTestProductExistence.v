(** Federer (1969), 4.1.8, p. 360: the separated tests exist
    in the actual compact test space. The smooth product and its
    compact support have been proved independently. The earlier
    opaque subspace corestriction supplies a witness here; consumers
    receive the independently specified test values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap AlternatingForms CurrentSpaces
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSpaceUP
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  CurrentCartesianDomain CurrentCartesianSmoothProductUP CurrentCartesianSmoothProductExistence
  CurrentCartesianSmoothProductSupport CurrentCartesianTestProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestProductExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Z := (R_n R (m+n)).
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation tc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).

(** Source for [current_cartesian_test_product_exists]: the pure
    tests p#alpha wedge q#beta in the characterising equations of
    Federer 4.1.8, p. 360 exist as genuine compact tests.
    Bilinearity follows from the injective original test inclusion.
    No product-current existence or density conclusion is assumed. *)
Theorem current_cartesian_test_product_exists k l:
  exists F:DA k->DB l->DC (k+l),
    @is_current_cartesian_test_product R h2 m n A B hA hB k l F.
Proof.
have [G hG]:=@current_cartesian_smooth_product_exists R h2 m n A B hA hB k l.
have [hGL hGR]:=hG.1.
have hValues:=hG.2.
pose S:=smooth_compact_support_subspace (hEC (k+l)).
pose inc:=smooth_test_inclusion (hEC (k+l)).
pose hInc:=smooth_test_space_laws (hEC (k+l)).
have hMember alpha beta:S (G alpha beta).
  exact:(@current_cartesian_smooth_product_compact_support R h2 m n A B hA hB k l
    G hG alpha beta).
pose L (alpha:DA k):Hom (DB l) (EC (k+l)):=
  @HomMap R (DB l) (EC (k+l)) (fun beta=>G alpha beta)
    (introT (asboolP _) (@hGR alpha)).
pose lift (alpha:DA k):Hom (DB l) (DC (k+l)):=
  @LinearSubspaceLift.map R (DB l) (DC (k+l)) (EC (k+l)) S inc hInc
    (L alpha) (@hMember alpha).
pose F (alpha:DA k) (beta:DB l):=lift alpha beta.
have hIncluded alpha beta:inc (F alpha beta)=G alpha beta.
  exact:(@LinearSubspaceLift.evaluation R (DB l) (DC (k+l)) (EC (k+l))
    S inc hInc (L alpha) (@hMember alpha) beta).
have hBilinear:bilinear F.
  split.
  - move=>beta c alpha alpha'.
    apply:(subspace_representation_injective hInc).
    have hGLinear:=@hGL beta c alpha alpha'.
    have hIncludedSum:=@hIncluded (c*:alpha+alpha') beta.
    have hBack:=congr2 (fun U V:EC (k+l)=>c*:U+V)
      (esym (@hIncluded alpha beta)) (esym (@hIncluded alpha' beta)).
    have hLinearInclusion:inc (c*:F alpha beta+F alpha' beta)=
        c*:inc (F alpha beta)+inc (F alpha' beta).
      exact:linearP.
    exact:(eq_trans hIncludedSum (eq_trans hGLinear (eq_trans hBack (esym hLinearInclusion)))).
  - move=>alpha;exact:(hom_linear (lift alpha)).
exists F;split;first exact:hBilinear.
move=>alpha beta z hz.
have hEvaluation:=congr1 (fun phi:EC (k+l)=>vc (k+l) phi z) (@hIncluded alpha beta).
exact:(eq_trans hEvaluation (@hValues alpha beta z hz)).
Qed.
End CurrentCartesianTestProductExistence.

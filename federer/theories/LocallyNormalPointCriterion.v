(** Federer (1969), 4.1.7, p. 358: T is
    locally normal exactly when near every
    point it agrees with a normal current.
    The converse uses the proved finite
    partition criterion for integration representation
    of T and its actual boundary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentContraction CurrentTestFormProduct CurrentBoundary CurrentTestExteriorDerivative CurrentBoundarySupport
  CurrentSupportGeometry CurrentSupportAgreement CurrentScalarCutoffs CurrentScalarPlateau
  CurrentIntegrationCriterion CurrentPointwiseRepresentation NormalCurrentsUP LocallyNormalScalarContraction
  SmoothCompactSet SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocallyNormalPointCriterion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation LN := (fun m=>@is_locally_normal_current R h2 n U hU m).
Local Notation N := (fun m=>@is_normal_current R h2 n U hU m).
Local Notation csupport := (fun m=>@current_support R h2 n U hU m).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).

(** Source for [locally_normal_near_point_normal]:
    every point of a locally normal
    current has a normal representative near
    it, Federer 4.1.7, p. 358,
    second equivalence, forward implication. *)
Theorem locally_normal_near_point_normal m (T:C m):
  LN m T->forall x,U x->exists S:C m,N m S /\~csupport m (T-S) x.
Proof.
move=>hT x hx.
have hIn:[set x] `<=` U by move=>z ->;exact:hx.
pose K:=@Build_smooth_compact_set R X NX hNX U [set x] hIn (@compact_set1 (real_norm_metric_space hNX) x).
have[gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU K.
pose a:=smooth_test_inclusion hE0 gamma.
pose S:=@current_contraction R h2 n 0 m U hU a T.
exists S;split;first exact:(@locally_normal_compact_scalar_contraction R h2 n U hU m gamma T hT).
have hAgreement:forall psi:@current_test_space R h2 n U hU m,
    @current_test_support R h2 n m U hU psi `<=` W ->
    @current_value R h2 n U hU m T psi=@current_value R h2 n U hU m S psi.
  move=>psi hPsi;rewrite current_contraction_evaluation.
  by rewrite (@current_scalar_test_local_plateau R h2 n m U hU W a hOne psi hPsi).
have hBound:=@current_support_difference_agreement R h2 n m U hU T S W hW hAgreement.
move=>hSupp;exact:(hBound x hSupp).2 (hKW x (erefl x)).
Qed.

(** Source for [locally_normal_point_criterion]: the
    original equivalence T locally normal iff
    each x admits normal S with
    x outside spt(T-S), Federer 4.1.7,
    p. 358. Both original support
    and degree-zero conventions are retained. *)
Theorem locally_normal_point_criterion m (T:C m):
  LN m T <->forall x,U x->exists S:C m,N m S /\~csupport m (T-S) x.
Proof.
split;first exact:locally_normal_near_point_normal.
move=>hLocal.
have hT:@is_integration_representable_current R h2 n m U hU T.
  apply:(@current_pointwise_representation R h2 n m U hU T)=>x hx.
  have[S [hS hOutside]]:=hLocal x hx.
  have[W [hW [hxW [hWU hAgree]]]]:=@current_agreement_near_point R h2 n m U hU T S x hx hOutside.
  exists W;split=>//;split=>//;split=>//;exists S;split=>//;exact:hS.1.1.
split=>//.
clear hT.
case:m T hLocal=>[|p] T hLocal;first by [].
apply:(@current_pointwise_representation R h2 n p U hU (bd p T))=>x hx.
have[S [hS hOutside]]:=hLocal x hx.
have[W [hW [hxW [hWU hAgree]]]]:=@current_agreement_near_point R h2 n p.+1 U hU T S x hx hOutside.
exists W;split=>//;split=>//;split=>//;exists (bd p S);split;first exact:hS.1.2.
move=>psi hPsi;rewrite !current_boundary_evaluation.
apply:hAgree=>z hz;apply:hPsi.
exact:(@current_test_exterior_support_subset R h2 n p U hU psi z hz).
Qed.
End LocallyNormalPointCriterion.

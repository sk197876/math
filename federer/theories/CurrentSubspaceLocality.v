(** Federer (1969), 4.1.12, p. 368: the
    original local-flatness criterion follows from a
    finite partition of unity on each compact test
    support. This supporting argument applies to any
    supplied current subspace stable under compact
    scalar multiplication. The actual spaces and support
    agreement are those of 4.1.1 and 4.1.7. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions
  classical_sets reals topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentContraction CurrentContractionLeftLinear CurrentProductLeftSupport CurrentTestFormProduct
  CurrentSupportGeometry CurrentSupportAgreement CurrentEvaluation
  SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation SmoothMultiplierUP
  SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence SmoothPartitionCompactSelection
  SmoothTestScalarMultiplier SmoothTestFiniteDecomposition CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSubspaceLocality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y0 := (A_m X R^o 0%N).
Local Notation NY0 := (@current_form_comass R h2 n 0%N).
Local Notation hNY0 := (@current_form_comass_real_norm R h2 n 0%N).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E0 := (@current_smooth_space R h2 n U hU 0%N).
Local Notation ev0 := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation DT0 := (@current_test_space R h2 n U hU 0%N).
Local Notation inc0 := (smooth_test_inclusion hE0).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation support := (@current_test_support R h2 n m U hU).
Local Notation csupport := (@current_support R h2 n U hU m).
Local Notation contract gamma := (@current_contraction R h2 n 0%N m U hU (inc0 gamma)).
Variable A:subspace C.
Hypothesis hStable:forall (gamma:DT0) (S:C),A S->A (contract gamma S).

(** Source for [current_subspace_germ_localisation]: if
    T agrees near every point with a member of
    an original subspace stable under compact scalar
    multiplication, every compact scalar multiple of T
    belongs to that subspace. This is the finite
    partition argument cited in Federer 4.1.12,
    p. 368, using the already proved partition
    of 4.1.1, p. 345. *)
Theorem current_subspace_germ_localisation (T:C):
  (forall x,U x->exists S:C,A S /\~csupport ((T-S)%R) x)->
  forall gamma:DT0,A (contract gamma T).
Proof.
move=>hLocal gamma.
pose Phi:set (set XT):=[set W|@open XT W /\ W `<=` U /\exists S:C,
  A S /\forall psi:DT,support psi `<=` W->action T psi=action S psi].
have hOpen W:Phi W->@open XT W by move=>[hW _];exact:hW.
have hDomain:(\bigcup_(W in Phi) W)=U.
  apply:funext=>x;apply:propext;split.
  - move=>[W [hW [hWU hModel]] hx];exact:hWU x hx.
  - move=>hx.
    have [S [hA hOutside]]:=hLocal x hx.
    have [W [hW [hWx [hWU hAgree]]]]:=@current_agreement_near_point R h2 n m U hU T S x hx hOutside.
    exists W=>//;split=>//;split=>//;exists S;by split.
have [J [I [v [hCount [hv hRef]]]]]:=@finite_norm_smooth_partition_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) Phi hOpen.
rewrite hDomain in hv.
have [K hK]:=smooth_test_support_bound hE0 gamma.
have [F [hFI hInactive]]:=smooth_partition_compact_active_selection hv K.
have hModels (s:F):exists S:C,A S /\forall psi:DT,
    support psi `<=` @real_function_support R XT (v (val s))->action T psi=action S psi.
  have [W [[hW [hWU [S [hA hAgree]]]] hSW]]:=hRef (val s) (@hFI (val s) (valP s)).
  exists S;split;first exact:hA.
  move=>psi hPsi;apply:hAgree=>x hx;exact:hSW x (hPsi x hx).
have [S hS]:=choice hModels.
pose hScalar (s:F) k:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) U (v (val s)) k (fun _ _=>Logic.I) hU
  (@smooth_partition_global_class R X NX hNX U J I v hv (val s) (@hFI (val s) (valP s)) k).
pose P (s:F):Hom DT0 DT0:=@smooth_test_scalar_multiplier R X Y0 NX NY0 hNX hNY0 U E0 ev0 hE0
  (v (val s)) (hScalar s).
have hP s:is_smooth_multiplier U (@current_test_value R h2 n U hU 0%N) (v (val s)) (P s).
  exact:smooth_test_scalar_multiplier_laws.
have hSum:=@smooth_test_finite_partition_identity R X Y0 NX NY0 hNX hNY0 U E0 ev0 hE0
  J I v hv K F hFI hInactive P hP gamma hK.
have hLinear:linear (fun g:DT0=>contract g T).
  move=>c g q.
  have hInc:inc0 (c*:g+q)=c*:inc0 g+inc0 q:=hom_linear inc0 c g q.
  rewrite hInc.
  exact:(@current_contraction_left_linear R h2 n 0%N m U hU T c (inc0 g) (inc0 q)).
pose Q:Hom DT0 C:=@HomMap R DT0 C (fun g=>contract g T) (introT (asboolP _) hLinear).
have hApplied:=congr1 Q hSum.
rewrite linear_sum in hApplied.
have hSame (s:F):Q (P s gamma)=contract (P s gamma) (S s).
  apply:current_values_extensional=>psi.
  have hQ:Q (P s gamma)=contract (P s gamma) T by [].
  rewrite hQ !current_contraction_evaluation.
  apply:(hS s).2=>x hx.
  have hLeft:=@current_test_form_product_left_support R h2 n 0%N m U hU
    (inc0 (P s gamma)) psi x hx.
  exact:(@smooth_test_scalar_multiplier_support R X Y0 NX NY0 hNX hNY0 U E0 ev0 hE0
    (v (val s)) (hScalar s) gamma x hLeft).
have hPieces (s:F):A (contract (P s gamma) (S s)).
  exact:(@hStable (P s gamma) (S s) (hS s).1).
have hClosedSum:A (\sum_(s:F) contract (P s gamma) (S s)).
  elim/big_rec: _=>[|s z _ hz];first exact:subspace_zero.
  exact:subspace_add (hPieces s) hz.
have hSumEquality:(\sum_(s:F) Q (P s gamma))=\sum_(s:F) contract (P s gamma) (S s).
  apply:eq_bigr=>s _;exact:hSame s.
have hCurrent:Q gamma=\sum_(s:F) contract (P s gamma) (S s):=
  eq_trans (esym hApplied) hSumEquality.
change (A (Q gamma));rewrite hCurrent;exact:hClosedSum.
Qed.
End CurrentSubspaceLocality.

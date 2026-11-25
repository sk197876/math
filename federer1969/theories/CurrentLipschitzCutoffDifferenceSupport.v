(** Federer (1969), 4.1.14, p. 371: the
    local cutoff formula is independent of every allowed
    scalar cutoff. Two cutoffs are one near the
    original support over the target test support. Their
    contracted-current difference therefore has support avoiding
    that inverse image. Only the original scalar contraction
    and local support laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero CurrentSpaces SmoothTestSpaces
  CurrentContraction CurrentContractionLeftLinear CurrentContractionSupport
  CurrentSupportGeometry CurrentSupportAgreement CurrentScalarPlateau.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzCutoffDifferenceSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation D0 := (@current_test_space R h2 n U hU 0%N).
Local Notation E0 := (@current_smooth_space R h2 n U hU 0%N).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation inc := (smooth_test_inclusion hE0).
Local Notation scalar := (@current_test_value R h2 n U hU 0%N).
Local Notation smooth := (@current_smooth_value R h2 n U hU 0%N).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation contract := (@current_contraction R h2 n 0%N m U hU).
Local Notation sourceTestSupport := (@current_test_support R h2 n m U hU).
Local Notation targetTestSupport := (@current_test_support R h2 nu m V hV).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation one := (@zero_form R X R^o 1).

(** Source for [current_scalar_contraction_difference_support_subset]:
    the difference of two scalar contractions cannot
    enlarge spt T, supporting cutoff independence in
    Federer 4.1.14, p. 371. T is arbitrary;
    no local flatness or measure representation is needed. *)
Lemma current_scalar_contraction_difference_support_subset (T:C) (gamma delta:E0):
  support (contract gamma T-contract delta T) `<=` support T.
Proof.
have hDifference:contract (gamma-delta) T=contract gamma T-contract delta T.
  exact:(linB (@current_contraction_left_linear R h2 n 0%N m U hU T)
    gamma delta).
rewrite -hDifference.
exact:(@current_contraction_support_subset R h2 n 0%N m U hU (gamma-delta) T).
Qed.

(** Source for [current_lipschitz_cutoff_difference_support]:
    every point in spt((T contracted gamma) minus
    (T contracted delta)) maps outside spt phi when
    both original interior plateau premises hold, supporting
    the all-cutoff local equation of Federer 4.1.14,
    p. 371. The target map has no regularity
    premise here, and the original current is arbitrary. *)
Theorem current_lipschitz_cutoff_difference_support (T:C) (f:X->Y)
    (phi:@current_test_space R h2 nu V hV m) (gamma delta:D0):
  (forall x,support T x->targetTestSupport phi (f x)->
    @interior (real_norm_metric_space hNX) [set z|scalar gamma z=one] x)->
  (forall x,support T x->targetTestSupport phi (f x)->
    @interior (real_norm_metric_space hNX) [set z|scalar delta z=one] x)->
  forall x,support (contract (inc gamma) T-contract (inc delta) T) x->
    ~targetTestSupport phi (f x).
Proof.
move=>hGamma hDelta x hx hPhi.
have hxT:support T x.
  exact:(@current_scalar_contraction_difference_support_subset T (inc gamma)
    (inc delta) x hx).
pose W:=(@interior (real_norm_metric_space hNX) [set z|scalar gamma z=one]) `&`
  (@interior (real_norm_metric_space hNX) [set z|scalar delta z=one]).
have hW:@open (real_norm_metric_space hNX) W.
  exact:openI (open_interior _) (open_interior _).
have hOneGamma:forall y,W y->smooth (inc gamma) y=one.
  move=>y hy;exact:interior_subset hy.1.
have hOneDelta:forall y,W y->smooth (inc delta) y=one.
  move=>y hy;exact:interior_subset hy.2.
have hAgree:forall psi:@current_test_space R h2 n U hU m,
    sourceTestSupport psi `<=` W->
    action (contract (inc gamma) T) psi=action (contract (inc delta) T) psi.
  move=>psi hPsi;rewrite !current_contraction_evaluation.
  rewrite (@current_scalar_test_local_plateau R h2 n m U hU W
    (inc gamma) hOneGamma psi hPsi).
  rewrite (@current_scalar_test_local_plateau R h2 n m U hU W
    (inc delta) hOneDelta psi hPsi).
  by [].
have hOutside:=@current_support_difference_agreement R h2 n m U hU
  (contract (inc gamma) T) (contract (inc delta) T) W hW hAgree.
apply:(hOutside x hx).2.
split;first exact:hGamma x hxT hPhi.
exact:hDelta x hxT hPhi.
Qed.
End CurrentLipschitzCutoffDifferenceSupport.

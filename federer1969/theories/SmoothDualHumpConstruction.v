(** Federer (1969), 4.1.1, p. 344: recursive
    compactly supported test selections for the common-
    support assertion. This is an auxiliary existence
    construction under failure of a common compact bound;
    no conclusion about weak convergence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothCompactSet SmoothCompactExhaustionUP SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation FunctionalSupportUP SmoothDualEscapingTest SmoothDualFunctionalSupport SmoothDualHumpUP
  CompactExhaustionVanishingFamily NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HumpWitnessConstruction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation Comp := (smooth_compact_set hNX U).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U E ev).
Variable T:nat->Hom E R^o.
Hypothesis hT:forall j,open_family_continuous (smooth_function_opens hD)
  (norm_open_family (@scalar_absolute_value_norm R)) (T j).
Variable Bound:nat->Comp.
Hypothesis hBound:forall j,tsupport (T j) `<=` smooth_compact_carrier (Bound j).
Variable K:nat->Comp.
Hypothesis hK:is_smooth_compact_exhaustion K.
Hypothesis hNoCommon:forall C:Comp,exists j,~(tsupport (T j) `<=` smooth_compact_carrier C).

(** Source for [smooth_dual_hump_choice_exists]: an actual
    escaping test is available at every compact stage,
    supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_choice_exists (C:Comp):exists q:nat*DT,
  (support q.2 `<=` (U `&` ~` smooth_compact_carrier C)) /\ T q.1 (inc q.2)<>0.
Proof.
have [j hj]:=hNoCommon C.
have [f [hf hn]]:=@smooth_dual_escaping_compact_test R X Y NX NY hNX hNY d b hb U hU E ev hE D hD
  (T j) C (hT j) hj.
by exists (j,f).
Qed.

(** Source for [smooth_dual_hump_choice]: private selection
    of the proved escaping data, supporting Federer
    4.1.1, p. 344. *)
Definition smooth_dual_hump_choice (C:Comp):nat*DT:=projT1 (cid (smooth_dual_hump_choice_exists C)).

(** Source for [smooth_dual_hump_choice_laws]: the selected
    data retain their actual support and nonzero value,
    supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_choice_laws C:
  (support (smooth_dual_hump_choice C).2 `<=` (U `&` ~` smooth_compact_carrier C)) /\
  T (smooth_dual_hump_choice C).1 (inc (smooth_dual_hump_choice C).2)<>0.
Proof. exact:(projT2 (cid (smooth_dual_hump_choice_exists C))). Qed.

(** Source for [smooth_dual_hump_step]: private recursive
    step, enlarging the compact bound and fixing one
    selected evaluation, supporting Federer 4.1.1,
    p. 344. *)
Definition smooth_dual_hump_step n (s:Comp*E):Comp*E:=
  let q:=smooth_dual_hump_choice s.1 in
  let c:=(n.+1%:R-T q.1 s.2)/T q.1 (inc q.2) in
  (smooth_compact_union (smooth_compact_union s.1 (K n.+1)) (Bound q.1),s.2+c*:inc q.2).

(** Source for [smooth_dual_hump_state]: finite recursion
    of the proved choices, an auxiliary witness for
    Federer 4.1.1, p. 344. *)
Fixpoint smooth_dual_hump_state n:Comp*E:=
  match n with 0%N=>(K 0%N,0) | m.+1=>smooth_dual_hump_step m (smooth_dual_hump_state m) end.

(** Source for [smooth_dual_hump_compact]: the current
    private compact bound, supporting Federer 4.1.1,
    p. 344. *)
Definition smooth_dual_hump_compact n:Comp:=(smooth_dual_hump_state n).1.

(** Source for [smooth_dual_hump_partial]: the current
    finite smooth partial sum, supporting Federer
    4.1.1, p. 344. *)
Definition smooth_dual_hump_partial n:E:=(smooth_dual_hump_state n).2.

(** Source for [smooth_dual_hump_index]: the selected
    original sequence index, supporting Federer 4.1.1,
    p. 344. *)
Definition smooth_dual_hump_index n:nat:=(smooth_dual_hump_choice (smooth_dual_hump_compact n)).1.

(** Source for [smooth_dual_hump_test]: the selected
    actual compact test, supporting Federer 4.1.1,
    p. 344. *)
Definition smooth_dual_hump_test n:DT:=(smooth_dual_hump_choice (smooth_dual_hump_compact n)).2.

(** Source for [smooth_dual_hump_coefficient]: the scalar
    forcing the next selected evaluation, supporting
    Federer 4.1.1, p. 344. Its denominator
    is proved nonzero by the choice laws. *)
Definition smooth_dual_hump_coefficient n:R:=
  (n.+1%:R-T (smooth_dual_hump_index n) (smooth_dual_hump_partial n))/
    T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test n)).

(** Source for [smooth_dual_hump_increment]: the actual
    scaled compact test added at this stage,
    supporting Federer 4.1.1, p. 344. *)
Definition smooth_dual_hump_increment n:E:=smooth_dual_hump_coefficient n*:inc (smooth_dual_hump_test n).

(** Source for [smooth_dual_hump_partial_successor]: the
    recursive state adds exactly the original increment,
    supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_partial_successor n:
  smooth_dual_hump_partial n.+1=smooth_dual_hump_partial n+smooth_dual_hump_increment n.
Proof. by []. Qed.

(** Source for [smooth_dual_hump_compact_successor]: the
    next bound contains the earlier bound, the next
    exhaustion compact and the selected functional bound,
    supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_compact_successor n:
  smooth_dual_hump_compact n.+1=
    smooth_compact_union (smooth_compact_union (smooth_dual_hump_compact n) (K n.+1))
      (Bound (smooth_dual_hump_index n)).
Proof. by []. Qed.

(** Source for [smooth_dual_hump_selected_value]: the
    next selected evaluation is the prescribed integer,
    supporting the contradiction in Federer 4.1.1,
    p. 344. *)
Theorem smooth_dual_hump_selected_value n:
  T (smooth_dual_hump_index n) (smooth_dual_hump_partial n.+1)=n.+1%:R.
Proof.
have hNonzero:= (smooth_dual_hump_choice_laws (smooth_dual_hump_compact n)).2.
have hDen:T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test n))!=0 by apply/eqP; exact hNonzero.
rewrite smooth_dual_hump_partial_successor /smooth_dual_hump_increment linearD linearZ.
change (T (smooth_dual_hump_index n) (smooth_dual_hump_partial n)+
  ((n.+1%:R-T (smooth_dual_hump_index n) (smooth_dual_hump_partial n))/
    T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test n)))*
    T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test n))=n.+1%:R).
by rewrite divfK // addrC subrK.
Qed.
(** Source for [smooth_dual_hump_partial_sum]: the recursive
    partial state is exactly the ordinary smooth sum,
    supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_partial_sum n:
  smooth_dual_hump_partial n=\sum_(j<n) smooth_dual_hump_increment j.
Proof.
elim:n=>[|n ih]; first by rewrite big_ord0.
by rewrite smooth_dual_hump_partial_successor big_ord_recr ih.
Qed.

(** Source for [smooth_dual_hump_compact_monotone]: recursive
    compact bounds increase, supporting the support
    selection in Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_compact_monotone m n:(m<=n)%N ->
  smooth_compact_carrier (smooth_dual_hump_compact m) `<=`
    smooth_compact_carrier (smooth_dual_hump_compact n).
Proof.
move=>hmn.
have hSucc l:smooth_compact_carrier (smooth_dual_hump_compact l) `<=`
    smooth_compact_carrier (smooth_dual_hump_compact l.+1).
  rewrite smooth_dual_hump_compact_successor; by move=>x hx; left; left.
have hShift q:smooth_compact_carrier (smooth_dual_hump_compact m) `<=`
    smooth_compact_carrier (smooth_dual_hump_compact (q+m)%N).
  elim:q=>[|q ih]; first by rewrite add0n.
  rewrite addSn=>x hx; exact:(@hSucc (q+m)%N x (ih x hx)).
have h:=hShift (n-m)%N; by rewrite (subnK hmn) in h.
Qed.

(** Source for [smooth_dual_hump_exhaustion_bound]: each
    stage contains the corresponding original exhaustion
    compact, supporting Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_exhaustion_bound n:
  smooth_compact_carrier (K n) `<=` smooth_compact_carrier (smooth_dual_hump_compact n).
Proof.
case:n=>[|n]; first by move=>x hx.
rewrite smooth_dual_hump_compact_successor; by move=>x hx; left; right.
Qed.

(** Source for [smooth_dual_hump_increment_vanishes]: every
    increment vanishes on its current compact bound,
    supporting local finiteness in Federer 4.1.1,
    p. 344. *)
Lemma smooth_dual_hump_increment_vanishes n x:
  smooth_compact_carrier (smooth_dual_hump_compact n) x ->ev (smooth_dual_hump_increment n) x=0.
Proof.
move=>hx.
have hZero:ev (inc (smooth_dual_hump_test n)) x=0.
  case:(pselect (ev (inc (smooth_dual_hump_test n)) x=0))=>// hn.
  have hSupp:support (smooth_dual_hump_test n) x.
    split; first exact:(smooth_compact_in_domain (smooth_dual_hump_compact n) x hx).
    exact (@subset_closure (real_norm_metric_space hNX)
      [set y:real_norm_metric_space hNX|value (smooth_dual_hump_test n) y<>0] x hn).
  have hOut:=(smooth_dual_hump_choice_laws (smooth_dual_hump_compact n)).1 x hSupp.
  exact:False_ind _ (hOut.2 hx).
by rewrite /smooth_dual_hump_increment (smooth_function_scale_value hE) hZero scaler0.
Qed.

(** Source for [smooth_dual_hump_later_evaluation_zero]: the
    compact enlargement makes every later increment invisible
    to every earlier selected functional, supporting
    Federer 4.1.1, p. 344. *)
Lemma smooth_dual_hump_later_evaluation_zero n m:(n<m)%N ->
  T (smooth_dual_hump_index n) (smooth_dual_hump_increment m)=0.
Proof.
move=>hnm.
have hZero:T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test m))=0.
  apply:(@smooth_dual_disjoint_support_zero R X Y NX NY hNX hNY d b hb U hU E ev hE D hD
    (T (smooth_dual_hump_index n)) (inc (smooth_dual_hump_test m)) (@hT (smooth_dual_hump_index n)))=>x ht hp.
  have hNext:smooth_compact_carrier (smooth_dual_hump_compact n.+1) x.
    rewrite smooth_dual_hump_compact_successor; right.
    exact:(@hBound (smooth_dual_hump_index n) x ht).
  have hIn:=@smooth_dual_hump_compact_monotone n.+1 m hnm x hNext.
  have hOut:=(smooth_dual_hump_choice_laws (smooth_dual_hump_compact m)).1 x hp.
  exact:hOut.2 hIn.
have hScale:T (smooth_dual_hump_index n)
    (smooth_dual_hump_coefficient m*:inc (smooth_dual_hump_test m))=
    smooth_dual_hump_coefficient m*:T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test m)):=
  linearZ_LR (hom_as_linear (T (smooth_dual_hump_index n)))
    (smooth_dual_hump_coefficient m) (inc (smooth_dual_hump_test m)).
change (T (smooth_dual_hump_index n)
  (smooth_dual_hump_coefficient m*:inc (smooth_dual_hump_test m))=0).
rewrite hScale.
change (smooth_dual_hump_coefficient m*:T (smooth_dual_hump_index n) (inc (smooth_dual_hump_test m))=0).
by rewrite hZero scaler0.
Qed.

(** Source for [smooth_dual_hump_exists]: failure of a
    common compact bound supplies an actual locally
    finite selection with the independent prescribed
    evaluation laws, supporting Federer 4.1.1,
    p. 344. *)
Theorem smooth_dual_hump_exists:exists (f:nat->E) (k:nat->nat),
  is_smooth_dual_hump NX U ev T f k.
Proof.
exists smooth_dual_hump_increment,smooth_dual_hump_index; constructor.
- apply:(@compact_exhaustion_vanishing_locally_finite R X NX hNX U K hK Y
    (fun j x=>ev (smooth_dual_hump_increment j) x))=>n x hx.
  exact:(@smooth_dual_hump_increment_vanishes n x (@smooth_dual_hump_exhaustion_bound n x hx)).
- move=>n; rewrite -smooth_dual_hump_partial_sum; exact:smooth_dual_hump_selected_value.
- exact:smooth_dual_hump_later_evaluation_zero.
Qed.
End HumpWitnessConstruction.

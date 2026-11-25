(** Federer (1969), 4.1.1, p. 344: a finite compact-set
    seminorm bound forces the functional support to be compact.
    The proof uses the original annihilation-open definition
    and locality of the exact higher differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology
  ContinuousMultilinearSealed SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionSupport SmoothLocalSupport SmoothDerivativeSeminormUP FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FunctionalSupportBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation functional_support := (@smooth_functional_support R X Y NX hNX U E ev).
Local Notation AOpen := (@smooth_functional_annihilation_open R X Y NX hNX U E ev).
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_functional_support_within_bound_compact]:
    the bound by M nu^i_K implies spt T contained in K,
    the argument for compact support in Federer 4.1.1, p. 344. *)
Theorem smooth_functional_support_within_bound_compact
    (K:smooth_compact_set hNX U) i (p:E->R)
    (hp:@is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p)
    (T:Hom E R^o) C :
  (forall f,`|T f|<=C * p f) ->
  functional_support T `<=` smooth_compact_carrier K.
Proof.
move=>hT x [hUx hSupp].
case:(pselect (smooth_compact_carrier K x))=>// hx.
apply:False_ind; apply:hSupp.
exists [set y|~smooth_compact_carrier K y]; split; last exact hx.
split.
- exact:closed_openC (compact_closed (@metric_hausdorff R XN) (smooth_compact_is_compact K)).
- move=>f hf.
  have hz:p f=0.
    apply:(@smooth_seminorm_disjoint_support_zero R X Y NX NY hNX hNY U hU E ev D hD
      K i p hp f)=>y hy hsy.
    exact:(hf y hsy) hy.
  have hZero:`|T f|<=0 by have h:=hT f; rewrite hz mulr0 in h.
  apply/eqP; by rewrite -normr_eq0 eq_le hZero normr_ge0.
Qed.

(** Source for [smooth_functional_support_compact]: once spt T
    lies in K, it is compact, completing the compact-support
    inference in Federer 4.1.1, p. 344. The relative U boundary
    is handled by intersection with K. *)
Theorem smooth_functional_support_compact (K:smooth_compact_set hNX U)
    (T:Hom E R^o):
  functional_support T `<=` smooth_compact_carrier K ->
  compact [set x:XN|functional_support T x].
Proof.
move=>hK.
pose G:set XN:=\bigcup_(W in [set W:set XN|AOpen T W]) W.
have hG:@open XN G.
  apply:bigcup_open=>W hW; exact:hW.1.
have hEq:[set x:XN|functional_support T x]=
    [set x:XN|smooth_compact_carrier K x] `&` ~` G.
  apply:funext=>x; apply:propext; split.
  - move=>hx; split; first exact:hK x hx.
    move=>[W hW hWx]; apply:hx.2; by exists W.
  - move=>[hx hOut]; split; first exact:smooth_compact_in_domain K x hx.
    move=>[W [hW hWx]]; apply:hOut; by exists W.
rewrite hEq; exact:compact_closedI (smooth_compact_is_compact K) (open_closedC hG).
Qed.
End FunctionalSupportBound.

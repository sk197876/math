(** Federer (1969), 4.1.1, p. 345: the support
    definition supplies an open cover on which either the
    distribution annihilates all supported tests or a
    prescribed disjointly supported test vanishes. This
    supporting cover is used with the original 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormOpenTopology SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces
  SmoothTestEvaluation FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestAnnihilationCover.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U DT value).
Local Notation ann := (@smooth_functional_annihilation_open R X Y NX hNX U DT value).

(** Source for [smooth_test_disjoint_annihilation_cover]:
    a disjointly supported test admits a cover by local
    annihilation sets and its open zero set, supporting
    T(phi)=0 in Federer 4.1.1, p. 345. No continuity
    of the functional is needed for this local step. *)
Theorem smooth_test_disjoint_annihilation_cover (T:Hom DT R^o) f:
  (forall x,tsupport T x ->~support f x) ->
  exists Phi:set (set XN),
    (forall W,Phi W ->@open XN W) /\
    (\bigcup_(W in Phi) W)=U /\
    forall W,Phi W ->W `<=` U /\ (ann T W \/ forall x,W x ->value f x=0).
Proof.
move=>hDisjoint.
have hOpenU:@open XN U.
  rewrite openE=>x hx.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
pose Phi:set (set XN):=[set W|@open XN W /\ W `<=` U /\
  (ann T W \/ forall x,W x ->value f x=0)].
have hCover:U `<=` \bigcup_(W in Phi) W.
  move=>x hx; case:(pselect (support f x))=>[hSupp|hNo].
  - have hSome:exists W,ann T W /\ W x.
      case:(pselect (exists W,ann T W /\ W x))=>// hNone.
      exact:False_ind _ (hDisjoint x (conj hx hNone) hSupp).
    have [V [[hV hAnn] hxV]]:=hSome.
    exists (V `&` U); last by split.
    split; first exact:openI hV hOpenU.
    split; first by move=>y [hy hu].
    left; split; first exact:openI hV hOpenU.
    move=>g hg; apply:hAnn=>y hy; exact:(hg y hy).1.
  - pose W:=U `&` ~` support f.
    have hClosed:=compact_closed (@metric_hausdorff R XN) (smooth_test_support_compact hE f).
    exists W; last by split.
    split; first exact:openI hOpenU (closed_openC hClosed).
    split; first by move=>y [hy hn].
    right=>y [hy hn].
    case:(pselect (value f y=0))=>// hne.
    apply:False_ind; apply:hn; split=>//.
    exact:(@subset_closure XN _ y hne).
have hDomain:(\bigcup_(W in Phi) W)=U.
  apply:funext=>x; apply:propext; split; last exact:hCover.
  move=>[W [hW [hWU hRest]] hx]; exact:hWU x hx.
exists Phi; split; first by move=>W [hW hRest].
split; first exact hDomain.
by move=>W [hW hRest].
Qed.
End TestAnnihilationCover.

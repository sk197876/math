(** Federer (1969), 4.1.1, p. 344: support of a smooth
    function is U intersected with the closure of its nonzero
    set. On compact subsets of U this is equivalent to vanishing
    outside the compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet SmoothFunctionSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_function_support]: direct definition of
    spt phi in Federer 4.1.1, p. 344. Closure is taken in the
    original source norm topology, and then intersected with U. *)
Definition smooth_function_support (R:realType) (X Y:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (E:lmodType R) (ev:E->X->Y) (f:E) : set X :=
  [set x|U x /\ closure [set y:real_norm_metric_space hNX|ev f y<>0] x].

Section SmoothSupportLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation T := (real_norm_metric_space hNX).

(** Source for [smooth_function_nonzero_in_support]: each nonzero
    value on U belongs to the support, supporting the fixed-support
    spaces of Federer 4.1.1, p. 344. *)
Lemma smooth_function_nonzero_in_support f x :
  U x -> ev f x<>0 -> support f x.
Proof. move=>hx hn; split=>//; exact:(@subset_closure T _ x hn). Qed.

(** Source for [smooth_function_compact_support_iff]: the support
    is contained in K exactly when the function vanishes off K,
    supporting D_K(U,Y) in Federer 4.1.1, p. 344. K is compact
    in the original source and contained in U. *)
Theorem smooth_function_compact_support_iff (K:smooth_compact_set hNX U) f :
  (support f `<=` smooth_compact_carrier K) <->
  forall x,~smooth_compact_carrier K x -> ev f x=0.
Proof.
split.
- move=>hK x hx; case:(pselect (U x))=>[hUx|hUx].
  + case:(pselect (ev f x=0))=>// hne.
    exact:False_ind _ (hx (hK x (smooth_function_nonzero_in_support hUx hne))).
  + exact:(smooth_function_evaluation_outside hE f hUx).
- move=>hZero x [hUx hCl].
  have hKC:@closed T [set z:T|smooth_compact_carrier K z]:=
    compact_closed (@metric_hausdorff R T) (smooth_compact_is_compact K).
  have hSub:[set z:T|ev f z<>0] `<=` [set z:T|smooth_compact_carrier K z].
    move=>z hn; case:(pselect (smooth_compact_carrier K z))=>// hz.
    exact:False_ind _ (hn (hZero z hz)).
  have h:=@closureS T _ _ hSub x hCl.
  by rewrite -((closure_id _).1 hKC) in h.
Qed.

(** Source for [smooth_function_supported_compact]: a function
    whose support is contained in K has compact support, as
    observed for D(U,Y) in Federer 4.1.1, p. 345. *)
Theorem smooth_function_supported_compact (K:smooth_compact_set hNX U) f :
  support f `<=` smooth_compact_carrier K ->
  compact [set x:T|support f x].
Proof.
move=>hK.
have hEq:[set x:T|support f x]=
    [set x:T|smooth_compact_carrier K x] `&`
      closure [set x:T|ev f x<>0].
  apply:funext=>x; apply:propext; split.
  - move=>hx; split; [exact:hK x hx|exact:hx.2].
  - move=>[hx hc]; split=>//; exact:(smooth_compact_in_domain K x hx).
rewrite hEq.
exact:compact_closedI (smooth_compact_is_compact K) (@closed_closure T _).
Qed.
End SmoothSupportLaws.

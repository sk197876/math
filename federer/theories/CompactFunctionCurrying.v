(** Federer (1969), 2.5.20, p. 114: the actual linear isomorphism S from
    norm-continuous maps X into K(Y) onto K(X times Y). All function-space
    operations use the abstract evaluation laws. Compactness includes empty
    spaces. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground CompactSupportFunctionUP
  CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionJointContinuity
  CompactProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Currying.
Variable R : realType.
Variables X Y : topologicalType.
Variable E : lmodType R.
Variable ev : E -> Y -> R.
Hypothesis hE : is_compact_function_space ev.

(** Source for [compact_function_families]: the space Q of
    all norm-continuous maps X into K(Y), Federer 2.5.20,
    p. 114. *)
Definition compact_function_families : set (X -> E) :=
  [set w | continuous (w : X -> real_norm_metric_space (compact_function_norm_laws hE))].

(** Source for [compact_function_uncurry]: the displayed
    map S(w)(x,y)=w(x)(y), Federer 2.5.20, p. 114. *)
Definition compact_function_uncurry (w : X -> E) (p : X*Y) := ev (w p.1) p.2.

(** Source for [compact_function_uncurry_linear]: linearity
    of S, Federer 2.5.20, p. 114; the formula holds
    for arbitrary total families before restricting to Q. *)
Lemma compact_function_uncurry_linear c u v :
  compact_function_uncurry (fun x => c*:u x+v x)=
    (fun p => c*compact_function_uncurry u p+compact_function_uncurry v p).
Proof.
apply: funext=> p; case: p=> x y.
exact: (@compact_function_evaluation_linear R Y E ev hE c (u x) (v x) y).
Qed.

(** Source for [compact_function_uncurry_injective]: injectivity
    of the linear isomorphism S, Federer 2.5.20, p. 114. *)
Lemma compact_function_uncurry_injective : injective compact_function_uncurry.
Proof.
move=> u v he; apply: funext=> x; apply: (@compact_function_evaluation_injective R Y E ev hE (u x) (v x)).
apply: funext=> y.
have hxy := congr1 (fun f : (X*Y)%type -> R => f (x,y)) he.
exact hxy.
Qed.

(** Source for [compact_function_uncurry_member]: S maps Q
    into K(X times Y), Federer 2.5.20, p. 114.
    Joint evaluation is continuous and the product is compact. *)
Theorem compact_function_uncurry_member :
  compact (@setT X) -> compact (@setT Y) -> forall w,
  compact_function_families w -> compactly_supported_continuous_functions (compact_function_uncurry w).
Proof.
move=> hX hY w hw; split.
- exact: (@compact_function_uncurry_continuous R Y E ev hE X w hw).
- have hXY : compact (@setT (X*Y)%type).
    have he : (@setT X) `*` (@setT Y)=setT by apply/seteqP; split=> p _; split.
    rewrite -he; exact: compact_setX hX hY.
  exact: subclosed_compact (@real_function_support_closed R (X*Y)%type _) hXY (@subsetT _ _).
Qed.

(** Source for [compact_function_uncurry_surjective]: the
    onto assertion for S in Federer 2.5.20, p. 114.
    Sections define the inverse family and compactness of Y
    proves its norm continuity. *)
Theorem compact_function_uncurry_surjective :
  hausdorff_space Y -> compact (@setT Y) -> forall f,
  compactly_supported_continuous_functions f ->
  exists w, compact_function_families w /\ compact_function_uncurry w=f.
Proof.
move=> hh hY f hf.
have hchoice x := compact_function_evaluation_surjective hE
  (@compact_product_second_section R X Y f x hh hf).
pose w x := projT1 (cid (hchoice x)).
have hw x : ev (w x)=(fun y => f (x,y)) := projT2 (cid (hchoice x)).
have he : compact_function_uncurry w=f.
  apply: funext=> p; case: p=> x y.
  exact (congr1 (fun g : Y -> R => g y) (hw x)).
exists w; split=> //.
apply: (@compact_function_curry_continuous R Y E ev hE X w hY).
change (continuous (compact_function_uncurry w : (X*Y)%type -> real_line_metric R)).
by rewrite he; exact: hf.1.
Qed.
End Currying.

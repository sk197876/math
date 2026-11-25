(** Federer (1969), 2.5.20, p. 114: normed vector laws of E=K(Y), derived
    from the abstract evaluation interface and sealed uniform norm. No
    nonempty-domain assumption is made; K(empty) is the zero space. Source
    context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP CompactFunctionSpaceUP CompactSupportFunctionUP
  CompactUniformNorm UniformFunctionNorm UniformFunctionNormUP UniformFunctionNormLaws
  FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Laws.
Variable R : realType.
Variable Y : topologicalType.
Variable V : lmodType R.
Variable ev : V -> Y -> R.
Hypothesis hv : is_compact_function_space ev.

(** Source for [compact_function_evaluation_zero]: zero evaluation
    in E=K(Y), supporting Federer 2.5.20, p. 114. *)
Lemma compact_function_evaluation_zero : ev 0=(fun _ => 0).
Proof.
apply: funext=> y.
have h := compact_function_evaluation_linear hv (-1) 0 0 y.
by rewrite scaler0 addr0 mulN1r addNr in h.
Qed.

(** Source for [compact_function_evaluation_add]: addition is
    pointwise in E=K(Y), Federer 2.5.20, p. 114. *)
Lemma compact_function_evaluation_add u v : ev (u+v)=(fun y => ev u y+ev v y).
Proof.
apply: funext=> y; have h := compact_function_evaluation_linear hv 1 u v y.
by rewrite scale1r mul1r in h.
Qed.

(** Source for [compact_function_evaluation_scale]: scalar
    multiplication is pointwise in E=K(Y), Federer 2.5.20, p. 114. *)
Lemma compact_function_evaluation_scale c u : ev (c*:u)=(fun y => c*ev u y).
Proof.
apply: funext=> y; have h := compact_function_evaluation_linear hv c u 0 y.
by rewrite addr0 compact_function_evaluation_zero addr0 in h.
Qed.

(** Source for [compact_function_evaluation_subtract]: differences
    are pointwise in E=K(Y), Federer 2.5.20, p. 114. *)
Lemma compact_function_evaluation_subtract u v : ev (u-v)=(fun y => ev u y-ev v y).
Proof.
rewrite -scaleN1r compact_function_evaluation_add compact_function_evaluation_scale.
by apply: funext=> y; rewrite mulN1r.
Qed.

(** Source for [compact_function_norm]: the displayed uniform
    norm of E=K(Y), Federer 2.5.20, p. 114, through
    the least-bound specification of 2.5.19, p. 113. *)
Definition compact_function_norm (v : V) := compact_support_uniform_norm (ev v).

(** Source for [compact_function_norm_laws]: supporting norm
    laws for the application of 2.5.12 in Federer 2.5.20,
    p. 114. All conclusions use only the abstract function
    space and uniform-norm interfaces. *)
Theorem compact_function_norm_laws : is_real_norm compact_function_norm.
Proof.
have hS := @compact_support_uniform_norm_laws R Y.
split.
- constructor.
  + move=> v; exact (@function_seminorm_nonnegative R Y
      (@compactly_supported_continuous_functions R Y) (@compact_support_uniform_norm R Y)
      hS (ev v) (compact_function_evaluation_member hv v)).
  + move=> c u; rewrite /compact_function_norm compact_function_evaluation_scale.
    exact (@function_seminorm_scale R Y
      (@compactly_supported_continuous_functions R Y) (@compact_support_uniform_norm R Y)
      hS c (ev u) (compact_function_evaluation_member hv u)).
  + move=> u v; rewrite /compact_function_norm compact_function_evaluation_add.
    exact (@function_seminorm_triangle R Y
      (@compactly_supported_continuous_functions R Y) (@compact_support_uniform_norm R Y)
      hS (ev u) (ev v) (compact_function_evaluation_member hv u) (compact_function_evaluation_member hv v)).
- move=> v hz; apply: (@compact_function_evaluation_injective R Y V ev hv v 0).
  rewrite compact_function_evaluation_zero; apply: funext=> y.
  have hn := compact_support_uniform_norm_specification (compact_function_evaluation_member hv v).
  change (compact_support_uniform_norm (ev v)=0) in hz.
  rewrite hz in hn; exact: uniform_function_norm_separates hn y.
Qed.

(** Source for [compact_function_evaluation_bound]: point
    evaluation is bounded by the displayed supremum norm in
    Federer 2.5.20, p. 114. *)
Lemma compact_function_evaluation_bound v y : `|ev v y|<=compact_function_norm v.
Proof.
exact: uniform_function_norm_bound (compact_support_uniform_norm_specification (compact_function_evaluation_member hv v)) y.
Qed.
End Laws.

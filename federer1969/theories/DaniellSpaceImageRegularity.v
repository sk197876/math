(** Federer (1969), 2.5.19, p. 113: "however u_#(phi) need not be K(Y)
    regular". On the compact space X of 2.5.15, with the evaluation lambda
    at the base point xi and the K(X) regular measure phi associated with
    lambda, the constant map u of X onto xi is continuous and proper,
    u_#(phi) represents u_*(lambda) = lambda, but u_#(phi) gives measure 0
    to X - {xi} while phi gives it measure 1; since the K(X) regular measure
    representing lambda is unique by 2.5.3, u_#(phi) is not K(X) regular. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology subtype_topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  MeasureUP MeasureBasic RealIntegralFunctionalUP FunctionLatticeRegularityUP
  FunctionLatticeRegularUniqueness CompactSupportFunctionUP CompactSupportFunctionLattice
  ProperMapUP MeasurePushforward UncountableProductExample DaniellSpacePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageRegularity.
Variable R : realType.
Variable J : choiceType.
Hypothesis hJ : ~ countable (@setT J).
Local Notation X := (@product_space R J).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation xi := (@base_point R J).

(** Source for [constant_base_map]: the constant map of X onto xi,
    Federer 2.5.19, p. 113. *)
Definition constant_base_map (x : X) : X := xi.

(** Source for [constant_base_map_continuous]: the constant map is
    continuous, Federer 2.5.19, p. 113. *)
Lemma constant_base_map_continuous : continuous constant_base_map.
Proof. by move=> x; exact: cst_continuous. Qed.

(** Source for [constant_base_map_proper]: the constant map is proper,
    since X is compact, Federer 2.5.19, p. 113. *)
Lemma constant_base_map_proper : is_proper_map constant_base_map.
Proof.
move=> K hK; case: (pselect (K xi))=> hx.
- have -> : constant_base_map @^-1` K = setT by apply/seteqP; split=> x //= _.
  exact: product_space_compact.
- have -> : constant_base_map @^-1` K = set0 by apply/seteqP; split=> x //=.
  exact: compact0.
Qed.

(** Source for [constant_base_map_daniell]: u_*(lambda) = lambda for the
    evaluation lambda at xi, Federer 2.5.19, p. 113. *)
Lemma constant_base_map_daniell :
  daniell_pushforward constant_base_map (@evaluation_functional R J) = @evaluation_functional R J.
Proof. by apply/funext. Qed.

(** Source for [pushforward_need_not_be_regular]: u_#(phi) represents
    u_*(lambda) but is not K(Y) regular, for the regular measure phi
    associated with the monotone Daniell integral lambda, Federer 2.5.19,
    p. 113. *)
Theorem pushforward_need_not_be_regular :
  exists (u : X -> X) (phi : set X -> \bar R),
    continuous u /\ is_proper_map u /\
    is_monotone_daniell_integral KX (@evaluation_functional R J) /\
    is_measure phi /\ is_real_integral_functional phi KX (@evaluation_functional R J) /\
    is_function_lattice_regular KX phi /\
    is_real_integral_functional (measure_pushforward u phi) KX
      (daniell_pushforward u (@evaluation_functional R J)) /\
    ~ is_function_lattice_regular KX (measure_pushforward u phi).
Proof.
have [phi [hm [hA hr]]] := @evaluation_regular_measure_exists R J.
have hpush := @daniell_pushforward_integral R X X constant_base_map constant_base_map_continuous
  constant_base_map_proper phi _ hm hA.
exists constant_base_map, phi; split; first exact: constant_base_map_continuous.
split; first exact: constant_base_map_proper.
split; first exact: (@evaluation_monotone_daniell R J).
do 4!(split=> //).
move=> hreg.
have hpush' : is_real_integral_functional (measure_pushforward constant_base_map phi) KX
    (@evaluation_functional R J) by rewrite -constant_base_map_daniell.
have hmp := measure_pushforward_is_measure constant_base_map hm.
have heq := function_lattice_regular_representation_unique
  (@compactly_supported_continuous_functions_lattice R X) hmp hm hpush' hA hreg hr
  (setT `\` [set xi]).
have h0 : measure_pushforward constant_base_map phi (setT `\` [set xi]) = 0%E.
  rewrite /measure_pushforward.
  have -> : constant_base_map @^-1` (setT `\` [set xi]) = set0.
    by apply/seteqP; split=> x //= [_ hx]; apply: hx.
  exact: measure_empty hm.
have h1 := phi_complement_base_point hJ hm hA hr.
by rewrite h0 h1 in heq; move: (@lte01 R); rewrite -heq ltxx.
Qed.

End ImageRegularity.

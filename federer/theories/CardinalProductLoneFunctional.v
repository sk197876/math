(** Federer (1969), 2.5.10, p. 100, and 2.5.11, p. 102: the question of
    2.5.10 asks, omitting the hypothesis that X is countably phi measurable,
    "whether there always exists a phi measurable function k such that
    mu(f)=integral f k d phi whenever f is phi summable", and "Example
    2.5.11 shows that in general the answer is no". Here mu is the linear
    functional of 2.5.7(ii) on all phi summable functions (the total space
    of the erratum p. 2, book p. 98 line 10), with M <= 1. In the example of
    2.5.11, L_1(phi)=L (CardinalProductLoneIdentity.v), so the functional
    mu(f)=integral f d(alpha_1 x beta_2) is itself defined on all phi
    summable functions; it coincides there with the extension mu_1 of 2.5.9,
    p. 100, which gives linearity and the bound |mu(f)| <= phi_(1)(f). No
    phi measurable real k represents it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalProductExample CardinalProductCounterexample
  CardinalProductLoneIdentity MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellIntegralUP RealIntegralFunctionalUP
  FunctionLatticeSeminormUP FunctionOperatorSeminorm VectorFunctionLattice TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP DominatedLoneExtensionUP DominatedLoneExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section LoneFunctional.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Hypothesis h2 : is_cardinal_successor (@setT J1) (@setT J2).
Variable phi : set (J1 * J2) -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi (@example_lattice R J1 J2 h1) (@example_lambda R J1 J2 h1).
Hypothesis hr : is_function_lattice_regular (@example_lattice R J1 J2 h1) phi.

Local Notation L := (@example_lattice R J1 J2 h1).
Local Notation hL := (@example_lattice_is_lattice R J1 J2 h1).
Local Notation lambda := (@example_lambda R J1 J2 h1).
Local Notation mu := (@example_mu R J1 J2 h1).

(** Source for [example_mu_absolute_bound]: the hypothesis
    |mu(f)| <= lambda(|f|) of 2.5.9, p. 100, for the functionals of
    Federer 2.5.11, p. 102, where "clearly mu(|f|) <= lambda(|f|)".
    Since mu is monotone and |f|+f, |f|-f are nonnegative members of
    L, |mu(f)| <= mu(|f|). *)
Lemma example_mu_absolute_bound (f : J1 * J2 -> R) :
  L f -> (`|mu f| <= lambda (fun x => `|f x|))%R.
Proof.
move=> hf.
have hM := @example_mu_monotone_daniell R J1 J2 h1.
have ha := @example_lattice_absolute R J1 J2 h1 f hf.
apply: le_trans (@example_mu_dominated R J1 J2 h1 f hf).
rewrite ler_norml; apply/andP; split.
- have hs : L (fun x => (`|f x| + f x)%R) by exact: (function_lattice_add hL ha hf).
  have h0 := @monotone_daniell_integral_nonnegative R _ L mu hL hM _ hs.
  have hn : function_nonnegative (fun x => (`|f x| + f x)%R).
    move=> x /=; have := lexx (`|f x|)%R; rewrite ler_norml=> /andP[hx _].
    by rewrite addrC -[(`|f x|)%R]opprK subr_ge0.
  have := h0 hn; rewrite (monotone_daniell_integral_add hM ha hf)=> hs0.
  by rewrite -subr_ge0 opprK addrC.
- apply: (monotone_daniell_integral_monotone hM hf ha)=> x; exact: ler_norm.
Qed.

(** Source for [example_lone_extension]: the extension mu_1 of
    2.5.9, p. 100, applied to the functionals of Federer 2.5.11,
    p. 102. *)
Definition example_lone_extension : (J1 * J2 -> R) -> R :=
  @dominated_lone_extension R _ L hL lambda mu phi hm
    (@example_lambda_monotone_daniell R J1 J2 h1) hA hr
    (@example_mu_daniell R J1 J2 h1) example_mu_absolute_bound.

(** Source for [example_lone_extension_specification]: the laws of
    mu_1 in Federer 2.5.9, p. 100, linearity on L_1(phi), agreement
    with mu on L and |mu_1(f)| <= phi_(1)(f), for the functionals of
    2.5.11, p. 102. *)
Lemma example_lone_extension_specification :
  is_dominated_lone_extension phi L mu example_lone_extension.
Proof.
exact: (@dominated_lone_extension_specification R _ L hL lambda mu phi hm
  (@example_lambda_monotone_daniell R J1 J2 h1) hA hr (@example_mu_daniell R J1 J2 h1)
  example_mu_absolute_bound).
Qed.

(** Source for [example_lone_extension_agrees]: on L_1(phi) the
    extension mu_1 of 2.5.9, p. 100, is the functional mu of
    Federer 2.5.11, p. 102, since L_1(phi)=L. *)
Lemma example_lone_extension_agrees (f : J1 * J2 -> R) :
  total_scalar_lp phi 1 f -> example_lone_extension f = mu f.
Proof.
move=> hf; have hS := example_lone_extension_specification.
exact: hS.2.1 f (@lone_in_example_lattice R J1 J2 h1 phi hm hA hr f hf).
Qed.

(** Source for [example_mu_lone_linear]: mu is a linear functional
    on all phi summable functions, Federer 2.5.10, p. 100, for the
    example 2.5.11, p. 102. *)
Lemma example_mu_lone_linear : is_linear_functional_on_functions (total_scalar_lp phi 1) mu.
Proof.
have [[hadd hscale] _] := example_lone_extension_specification.
have hV := @total_scalar_lp_vector_lattice R _ phi hm 1 (lexx _).
split.
- move=> f g hf hg.
  have hfg := function_lattice_add hV.1 hf hg.
  rewrite -(example_lone_extension_agrees hfg) -(example_lone_extension_agrees hf).
  by rewrite -(example_lone_extension_agrees hg); exact: hadd.
- move=> c f hf.
  have hcf := hV.2.2 c f hf.
  rewrite -(example_lone_extension_agrees hcf) -(example_lone_extension_agrees hf).
  exact: hscale.
Qed.

(** Source for [example_mu_lone_bound]: the bound
    |mu(f)| <= phi_(1)(f) for every phi summable f, inherited from
    mu_1 in Federer 2.5.9, p. 100, for the example 2.5.11, p. 102. *)
Lemma example_mu_lone_bound (f : J1 * J2 -> R) :
  total_scalar_lp phi 1 f -> (`|mu f| <= finite_total_scalar_lp_norm phi 1 f)%R.
Proof.
move=> hf; have hS := example_lone_extension_specification.
rewrite -(example_lone_extension_agrees hf); exact: hS.2.2 f hf.
Qed.

(** Source for [example_mu_operator_seminorm]: the number M of
    Federer 2.5.7, p. 98, erratum p. 2, book p. 98 line 11, is at most one for
    mu on all phi summable functions in the example 2.5.11,
    p. 102; in particular M < infinity as in the question of 2.5.10,
    p. 100. *)
Lemma example_mu_operator_seminorm :
  function_operator_seminorm (total_scalar_lp phi 1) mu (finite_total_scalar_lp_norm phi 1) <= 1.
Proof.
apply: (@function_operator_seminorm_least_bound R _ _ mu _ 1%R ler01)=> f hf.
by rewrite mul1r; exact: example_mu_lone_bound.
Qed.

(** Source for [example_lone_no_density]: Federer 2.5.10, p. 100,
    and 2.5.11, p. 102: no phi measurable real function k
    satisfies mu(f)=integral f k d phi whenever f is phi summable;
    such a k would represent mu on L. *)
Theorem example_lone_no_density (k : J1 * J2 -> R) :
  ~ is_real_lattice_density phi (total_scalar_lp phi 1) mu k.
Proof.
move=> [hk hrep]; apply: (@example_no_density R J1 J2 h1 h2 phi hm hA hr k).
split=> // f hf; apply: hrep.
by rewrite (@example_lone_identity R J1 J2 h1 phi hm hA hr).
Qed.

End LoneFunctional.

(** Source for [federer_2_5_10_negative_answer_lone]: the sentence
    "Example 2.5.11 shows that in general the answer is no" in
    Federer 2.5.10, p. 100, in the full form of the question: under
    the cardinal hypotheses of 2.5.11, p. 102, the L regular measure
    phi of lambda satisfies L_1(phi)=L, the functional mu is linear
    on all phi summable functions with M <= 1, and no phi measurable
    real k satisfies mu(f)=integral f k d phi whenever f is phi
    summable. The hypotheses |mu(f)| <= lambda(|f|) of 2.5.9 and the
    Daniell property of mu on L are included. *)
Theorem federer_2_5_10_negative_answer_lone (R : realType) (J1 J2 : choiceType)
    (h1 : is_cardinal_successor (@setT nat) (@setT J1))
    (h2 : is_cardinal_successor (@setT J1) (@setT J2)) :
  exists (L : set (J1 * J2 -> R)) (lambda mu : (J1 * J2 -> R) -> R) (phi : set (J1 * J2) -> \bar R),
    is_function_lattice L /\ is_monotone_daniell_integral L lambda /\
    is_measure phi /\ is_real_integral_functional phi L lambda /\ is_function_lattice_regular L phi /\
    is_daniell_integral L mu /\
    (forall f, L f -> (`|mu f| <= lambda (fun x => `|f x|))%R) /\
    total_scalar_lp phi 1 = L /\
    is_linear_functional_on_functions (total_scalar_lp phi 1) mu /\
    function_operator_seminorm (total_scalar_lp phi 1) mu (finite_total_scalar_lp_norm phi 1) <= 1 /\
    forall k : J1 * J2 -> R, ~ is_real_lattice_density phi (total_scalar_lp phi 1) mu k.
Proof.
have [phi [hm [hA hr]]] := @example_regular_measure_exists R J1 J2 h1.
exists (@example_lattice R J1 J2 h1), (@example_lambda R J1 J2 h1), (@example_mu R J1 J2 h1), phi.
split; first exact: example_lattice_is_lattice.
split; first exact: example_lambda_monotone_daniell.
split=> //; split=> //; split=> //.
split; first exact: example_mu_daniell.
split; first by move=> f hf; exact: (example_mu_absolute_bound hf).
split; first exact: (example_lone_identity hm hA hr).
split; first exact: (example_mu_lone_linear hm hA hr).
split; first exact: (example_mu_operator_seminorm hm hA hr).
by move=> k; exact: (example_lone_no_density h2 hm hA hr (k := k)).
Qed.

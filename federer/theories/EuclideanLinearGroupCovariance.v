(** Federer (1969), 2.7.16, p. 135: "The class H = {f : chi(f) = |det
    f|^{-1}} is a subgroup of GL(n, R), the (general) linear group of R^n
    ... Thus L^n is |det|^{-1} covariant with respect to the action of GL(n,
    R) on R^n", and "In case n >= 2 the special linear group SL(n, R) =
    GL(n, R) cap {f : det(f) = 1} acts transitively on R^n ~ {0}, and L^n is
    invariant with respect to the action of SL(n, R)". The groups are
    represented by the linear endomorphisms f of R^n with det f <> 0,
    respectively det f = 1, acting by evaluation; only the action and the
    character enter the definitions of 2.7.1, p. 122, and the topology of
    GL(n, R) is not needed for them. The covariance identity int u o f dL^n
    = |det f|^{-1} int u dL^n for u in K(R^n) comes from f_#(L^n) = |det
    f|^{-1} L^n (EuclideanLebesgueDeterminant.v) and the corresponding
    identity of integrals (EuclideanLebesgueLinear.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNormedTopology MeasureUP MeasureBasic CompactSupportFunctionUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MonotoneDaniellIntegralUP CovariantIntegralUP EuclideanLebesgue
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLebesgueHaar EuclideanLinearMaps
  EuclideanLebesgueLinear EuclideanLebesgueDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LinearGroups.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation K := (@compactly_supported_continuous_functions R E).

(** Source for [euclidean_general_linear]: "GL(n, R), the (general)
    linear group of R^n", Federer 2.7.16, p. 135: the linear
    endomorphisms f of R^n with det f <> 0. Definition. *)
Definition euclidean_general_linear : Type := {f : {linear V -> V} | euclidean_det f != 0}.

(** Source for [euclidean_special_linear]: "SL(n, R) = GL(n, R) cap
    {f : det(f) = 1}", Federer 2.7.16, p. 135. Definition. *)
Definition euclidean_special_linear : Type := {f : {linear V -> V} | euclidean_det f == 1}.

(** Source for [general_linear_action]: the action of GL(n, R) on R^n,
    A(f, x) = f(x), Federer 2.7.16, p. 135, curried as in 2.7.1, p. 121.
    Definition. *)
Definition general_linear_action (g : euclidean_general_linear) (x : E) : E := sval g x.

(** Source for [special_linear_action]: the action of SL(n, R) on R^n,
    Federer 2.7.16, p. 135. Definition. *)
Definition special_linear_action (g : euclidean_special_linear) (x : E) : E := sval g x.

(** Source for [euclidean_lebesgue_linear_integral]: Federer 2.7.16,
    p. 135: int u o f dL^n = |det f|^{-1} int u dL^n for u in K(R^n)
    and det f <> 0, the identity of integrals behind
    f_#(L^n) = |det f|^{-1} L^n. Supporting theorem. *)
Theorem euclidean_lebesgue_linear_integral (f : {linear V -> V}) : euclidean_det f != 0 ->
  forall u, K u -> (@euclidean_lebesgue_integral R n) (u \o (f : E -> E)) =
    `|euclidean_det f|^-1 * (@euclidean_lebesgue_integral R n) u.
Proof.
move=> hdet u hu.
have hinj := (euclidean_det_injective f).1 hdet.
have [g [hfg hgf]] := euclidean_linear_inverse hinj.
have [c [hc hI hS]] := euclidean_linear_pushforward_scale hfg hgf.
have hc1 : c = `|euclidean_det f|^-1.
  have h1 := hS [set x : E | forall i, 0 < x i < 1].
  rewrite (euclidean_lebesgue_linear_pushforward hdet) euclidean_unit_cube !mule1 in h1.
  by move: h1=> /eqP; rewrite eqe eq_sym=> /eqP.
by rewrite (hI u hu) hc1.
Qed.

(** Source for [euclidean_lebesgue_general_linear_covariant]: Federer
    2.7.16, p. 135, "Thus L^n is |det|^{-1} covariant with respect to the
    action of GL(n, R) on R^n", in the sense of 2.7.1, p. 122: L^n is the
    K(R^n) regular measure associated with the monotone Daniell integral
    u |-> int u dL^n, which satisfies
    int u(f(x)) dL^n x = |det f|^{-1} int u dL^n. Direct formalisation. *)
Theorem euclidean_lebesgue_general_linear_covariant :
  is_covariant_measure general_linear_action (fun g => `|euclidean_det (sval g)|^-1) Leb.
Proof.
exists (@euclidean_lebesgue_integral R n); split.
- exact: euclidean_lebesgue_integral_monotone.
- move=> u g hu; exact: (euclidean_lebesgue_linear_integral (svalP g) hu).
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_integral_represents.
- exact: euclidean_lebesgue_function_lattice_regular.
Qed.

(** Source for [euclidean_lebesgue_special_linear_invariant]: Federer
    2.7.16, p. 135, "L^n is invariant with respect to the action of
    SL(n, R)", in the sense of 2.7.1, p. 122. Direct formalisation; the
    case n >= 2 of the book is not needed for this assertion. *)
Theorem euclidean_lebesgue_special_linear_invariant : is_invariant_measure special_linear_action Leb.
Proof.
exists (@euclidean_lebesgue_integral R n); split.
- exact: euclidean_lebesgue_integral_monotone.
- move=> u g hu; have hdet : euclidean_det (sval g) != 0 by rewrite (eqP (svalP g)) oner_eq0.
  rewrite (euclidean_lebesgue_linear_integral hdet hu) (eqP (svalP g)) normr1 invr1.
  by [].
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_integral_represents.
- exact: euclidean_lebesgue_function_lattice_regular.
Qed.

(** Source for [euclidean_lebesgue_origin_null]: Federer 2.7.16,
    p. 135, "which really does not matter because L^n{0} = 0", for
    n >= 1. Direct formalisation. *)
Theorem euclidean_lebesgue_origin_null : (1 <= n)%N -> Leb [set (0 : E)] = 0%:E.
Proof.
case: n=> [//|m] _.
apply/eqP; rewrite eq_le (measure_nonnegative (euclidean_lebesgue_is_measure R m.+1)) andbT.
have hsub : [set (0 : inner_metric_space (@euclidean_inner_productP R m.+1))] `<=`
    [set x | forall i, 0 <= x i <= 0].
  by move=> x -> i; rewrite ffunE lexx.
apply: le_trans (@measure_mono R _ _ (euclidean_lebesgue_is_measure R m.+1) _ _ hsub) _.
rewrite (@euclidean_closed_box R m.+1 (fun _ => 0) (fun _ => 0)) // .
by rewrite subrr prodr_const card_ord expr0n.
Qed.

(** Source for [general_linear_action_not_transitive]: Federer 2.7.16,
    p. 135, "This action is not transitive": for n >= 1 no f in
    GL(n, R) maps 0 to a nonzero point. Direct formalisation. *)
Theorem general_linear_action_not_transitive (y : E) :
  y != 0 -> forall g : euclidean_general_linear, general_linear_action g 0 != y.
Proof. by move=> hy g; rewrite /general_linear_action linear0 eq_sym. Qed.

End LinearGroups.

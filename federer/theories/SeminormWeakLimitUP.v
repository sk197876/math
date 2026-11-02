(** Federer (1969), 2.9.23, pp. 168–169: weak convergence of the difference
    quotients means convergence under every continuous real linear
    functional. We specify the continuous dual of a seminormed space by the
    equivalent finite-bound law. This agrees with the dual of its separated
    quotient, without changing Federer's function-valued L1 convention
    (2.4.12, pp. 86–87). The local Federer erratum has no entry for this
    example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import RealCurveDerivativeUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_bounded_real_functional]: supporting dual
    specification for Federer 2.9.23, p. 169: a linear map
    is bounded by a finite nonnegative multiple of the L1 seminorm.
    The zero functional and the zero seminorm are included. *)
Definition seminorm_bounded_real_functional (R : realType) (E : lmodType R)
    (N : E -> R) (a : {linear E -> R^o}) :=
  exists C : R, 0<=C /\ forall v, `|a v|<=C*N v.

(** Source for [punctured_seminorm_weak_limit]: direct weak-limit
    meaning of the final sentence of Federer 2.9.23, p. 169.
    All bounded linear functionals and all sufficiently small
    nonzero increments are quantified, rather than a sequence. *)
Definition punctured_seminorm_weak_limit (R : realType) (E : lmodType R)
    (N : E -> R) (u : R -> E) (v : E) :=
  forall a : {linear E -> R^o}, seminorm_bounded_real_functional N a ->
    punctured_real_limit (fun h => a (u h)) (a v).

(** Source for [punctured_seminorm_limit_weak]: supporting implication
    from seminorm convergence to weak convergence in Federer 2.9.23,
    p. 169. It uses only a bound on each linear functional;
    definiteness and completeness are unnecessary. *)
Lemma punctured_seminorm_limit_weak (R : realType) (E : lmodType R)
    (N : E -> R) (u : R -> E) (v : E) :
  (forall w, 0<=N w) -> punctured_norm_limit N u v ->
  punctured_seminorm_weak_limit N u v.
Proof.
move=> hN hu a [C [hC hA]] e he.
have hCp : 0<C+1 by lra.
have hep : 0<e/(C+1) by rewrite divr_gt0.
have [d [hd hU]] := hu _ hep; exists d; split=> // h hh.
have hsmall := hU h hh.
have hB := hA (u h-v); rewrite linearB in hB.
have hN0 := hN (u h-v).
have hprod : (C+1)*N (u h-v)<e.
  by move: hsmall; rewrite ltr_pdivlMr // mulrC.
have hcmp : C*N (u h-v)<=(C+1)*N (u h-v) by nra.
exact: le_lt_trans hB (le_lt_trans hcmp hprod).
Qed.

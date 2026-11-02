(** Local correction to Federer (1969), 2.4.12, p. 86, norming-functional
    corollary following the Hahn–Banach proof. The printed definition allows
    sigma(v)=infinity, whereas the conclusion asks a real-valued linear
    functional to attain sigma(v). Thus the corollary needs
    sigma(v)<infinity. The scan at physical page 103 confirms the printed
    statement. No entry in Federer's May-1987 erratum corrects this
    corollary; its pp. 1–2 corrections to book pp. 86–88 concern function
    spaces and density instead. Source context: ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [discrete_infinite_seminorm]: local counterexample
    to the unrestricted norming-functional corollary of Federer
    2.4.12, p. 86: zero at zero and infinity at
    every nonzero scalar. This construction is not asserted
    by Federer or by his erratum. *)
Definition discrete_infinite_seminorm (R : realType) (x : R) : \bar R :=
  if x == 0%R then 0 else +oo.

(** Source for [discrete_infinite_seminorm_laws]: verification
    that the counterexample satisfies the exact seminorm laws
    printed in Federer 2.4.12, p. 86, including
    zero-times-infinity=zero. *)
Lemma discrete_infinite_seminorm_laws (R : realType) :
  @is_extended_seminorm R R^o (@discrete_infinite_seminorm R).
Proof.
constructor.
- move=> x; rewrite /discrete_infinite_seminorm; case: ifP=> _; [exact: lexx|exact: leey].
- move=> c x; change (discrete_infinite_seminorm (c*x)%R = `|c|%:E * discrete_infinite_seminorm x).
  rewrite /discrete_infinite_seminorm mulf_eq0.
  case: (eqVneq c 0%R)=> [->|hc].
  + by rewrite ?eqxx normr0 mul0e.
  + case: (eqVneq x 0%R)=> [hx|hx].
    * by rewrite /= mule0.
    * rewrite /=.
      rewrite gt0_muley // lte_fin normr_gt0; exact hc.
- move=> x y; change (discrete_infinite_seminorm (x+y)%R <= discrete_infinite_seminorm x + discrete_infinite_seminorm y).
  rewrite /discrete_infinite_seminorm.
  case: (eqVneq x 0%R)=> [->|hx].
  + rewrite add0r ?eqxx add0e; exact: lexx.
  + by case: ifP=> _; case: ifP=> _; rewrite ?adde0 ?addye ?leey.
Qed.

(** Source for [infinite_seminorm_has_no_norming_functional]:
    counterexample to the corollary in Federer 2.4.12,
    p. 86, when the missing finiteness premise is omitted.
    Every real-valued functional, linear or otherwise, has a
    finite value at one and cannot attain this seminorm there. *)
Theorem infinite_seminorm_has_no_norming_functional (R : realType) :
  ~ exists g : {linear R^o -> R^o},
    (g 1%R)%:E = discrete_infinite_seminorm (1 : R).
Proof.
move=> [g hg]; move: hg; rewrite /discrete_infinite_seminorm oner_eq0.
by move=> hfalse; discriminate hfalse.
Qed.

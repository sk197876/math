(** Federer (1969), 1.7.13, p. 37: public interface to d=dist(a,C), with
    nonempty C and no closedness assumption. Later arguments use only these
    laws, not the witness construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm InnerSetDistanceUP InnerSetDistanceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Distance.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable a : V.
Variable C : set V.
Hypothesis hne : C !=set0.

(** Source for [inner_set_distance]: Federer 1.7.13,
    p. 37, the distance d supplied by its sealed specification. *)
Definition inner_set_distance := @InnerSetDistance.distance R V B hB a C hne.

(** Source for [inner_set_distanceP]: Federer 1.7.13,
    p. 37, the public distance obeys the infimum laws. *)
Theorem inner_set_distanceP : is_inner_set_distance hB a C inner_set_distance.
Proof. exact: InnerSetDistance.laws. Qed.

(** Source for [inner_set_distance_inf]: Federer 1.7.13,
    p. 37, the defining display d=inf{|a-x|:x in C}.
    This identification follows from the abstract lower-bound and
    approximation laws without exposing the existence witness. *)
Theorem inner_set_distance_inf :
  inner_set_distance = inf ((fun x => inner_norm hB (a-x)) @` C).
Proof.
pose D := (fun x => inner_norm hB (a-x)) @` C.
have hn : D !=set0.
  have [x hx] := hne; exists (inner_norm hB (a-x)); by exists x.
have hb : has_lbound D.
  exists 0 => t [x hx <-]; exact: inner_norm_nonnegative.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: lb_le_inf hn _ => t [x hx <-].
  exact (@inner_set_distance_lower_law R V B hB a C inner_set_distance inner_set_distanceP x hx).
- apply: (@inner_set_distance_greatest_lower_bound R V B hB a C
    inner_set_distance inner_set_distanceP (inf D)) => x hx.
  apply: (ge_inf hb); by exists x.
Qed.
End Distance.

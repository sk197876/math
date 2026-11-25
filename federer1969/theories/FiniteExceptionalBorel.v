(** Federer (1969), 2.2.15, p. 71, final target criterion: supporting Borel
    interpolation on finitely many real inputs. A map constant off a finite
    set is Borel when source singletons are closed. This is a proof
    ingredient, not an additional assertion printed in the book. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_metric_set_borel]: supporting finite-set
    Borel fact for Federer 2.2.15, p. 71, using
    closed singletons and the closure laws of 2.2.1, p. 60. *)
Lemma finite_metric_set_borel (R : realType) (X : metricType R) (A : set X) :
  finite_set A -> borel_set A.
Proof.
move=> hA.
have he : A = \bigcup_(x in A) [set x].
  apply/seteqP; split; first by move=> x hx; exists x.
  by move=> x [y hy ->].
rewrite he; apply: borel_set_countable_union (finite_set_countable hA) _.
move=> x hx; apply: closed_borel_set.
apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [finite_exceptional_map_borel]: supporting
    interpolation lemma for the necessity of Federer 2.2.15,
    p. 71. Each open preimage is a finite set,
    together with the complement of the finite exceptional set
    precisely when the constant value belongs to that open set. *)
Lemma finite_exceptional_map_borel (R : realType) (X : metricType R)
    (Y : topologicalType) (F : set X) (f : X -> Y) y0 :
  finite_set F -> (forall x, ~ F x -> f x = y0) -> is_borel_function f.
Proof.
move=> hF hf U hU.
pose A := F `&` (f @^-1` U).
have hA : borel_set A := finite_metric_set_borel (finite_setIl _ hF).
case: (pselect (U y0))=> hy.
- have he : f @^-1` U = A `|` ~` F.
    apply/seteqP; split.
    + move=> x hx; case: (pselect (F x))=> hfx; [left|right]=> //; by split.
    + move=> x [[_ hx]|hx]=> //; change (U (f x)); by rewrite (hf x hx).
  rewrite he; exact: (@borel_family_binary_union X setT _ (borel_sets_family X)
    A (~` F) hA (borel_set_complement (finite_metric_set_borel hF))).
- have he : f @^-1` U = A.
    apply/seteqP; split; last by move=> x [_ hx].
    move=> x hx; split=> //; case: (pselect (F x))=> // hfx.
    exfalso; apply: hy.
    change (U (f x)) in hx; by rewrite (hf x hfx) in hx.
  by rewrite he.
Qed.

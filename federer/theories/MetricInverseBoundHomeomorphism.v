(** General metric topology supporting the inverse-function theorem
    in Federer (1969), 3.1.1, p. 210. A lower distance bound proves
    continuity of the inverse of a continuous bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import HomeomorphismUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_inverse_bound_homeomorphism]: supporting
    passage from the inverse Lipschitz estimate to a homeomorphism in
    Federer 3.1.1, p. 210. The inverse witness is constructed inside this
    opaque existence proof; downstream statements use only the abstract
    homeomorphism laws. *)
Lemma metric_inverse_bound_homeomorphism (R : realType)
    (S T : metricType R) (f : S -> T) (K : R) :
  continuous f -> injective f -> (forall y, exists x, f x=y) ->
  0 <= K -> (forall x z, mdist x z <= K*mdist (f x) (f z)) ->
  is_homeomorphism f.
Proof.
move=> hc hi hs hK hb.
pose g y := sval (constructive_indefinite_description (hs y)).
have hfg : cancel g f by move=> y; exact: svalP (constructive_indefinite_description (hs y)).
have hgf : cancel f g by move=> x; apply: hi; rewrite hfg.
exists g; constructor=> //.
apply: (@metric_fixed_lipschitz_continuous R T S g K hK)=> y w.
by have hh := hb (g y) (g w); rewrite !hfg in hh.
Qed.

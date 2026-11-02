(** Supporting closure passage for Federer (1969), 2.10.3, p. 172, compact
    covering alternative. A continuous real-valued function on a finite
    product retains a bound when each coordinate set is replaced by its
    closure. Prove this by closed single-coordinate sublevels and finite
    iteration, without a separate theorem about product closures. This is
    general topology supporting the printed claim, not an extra assertion
    attributed to Federer. Source context and the exterior-product context:
    ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype.
From Federer Require Import SeparateAffineHullBound RealMetricBackground EuclideanCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Import numFieldTopology.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_replacement_continuous]: supporting
    continuity of a single-variable insertion for the
    endpoint map in Federer 2.10.3, p. 172. The
    product topology is characterized coordinate by coordinate. *)
Lemma coordinate_replacement_continuous (T : topologicalType) (I : eqType)
    (p : I -> T) (i : I) : continuous (fun x : T => coordinate_replacement p i x).
Proof.
apply: (@coordinate_family_continuous T I (fun _ => T)
  (fun j x => coordinate_replacement p i x j)).
move=> j; rewrite /coordinate_replacement; case: (j==i).
- by move=> x; exact: cvg_id.
- exact: cst_continuous.
Qed.

(** Source for [continuous_finite_coordinate_closure_bound]:
    supporting finite-variable closure argument for the
    compact-cover equality of Federer 2.10.3, p. 172.
    Closed real sublevels pass each coordinate's bound
    to its closure. Empty finite products are included. *)
Theorem continuous_finite_coordinate_closure_bound (R : realType)
    (T : topologicalType) (I : finType) (F : (I -> T) -> real_line_metric R)
    (A : set T) (q : R) : continuous F ->
  (forall p, (forall i, A (p i)) -> F p<=q) ->
  forall p, (forall i, closure A (p i)) -> F p<=q.
Proof.
move=> hF hA p hp.
have hstep : forall s : seq I, uniq s -> forall v : I -> T,
    (forall i, i \in s -> closure A (v i)) ->
    (forall i, i \notin s -> A (v i)) -> F v<=q.
  elim=> [|i s ih] hs v hvclos hvAout.
  - apply: hA=> j; exact: hvAout j (erefl true).
  - have /andP[his hs'] := hs.
    pose f (x : T) := F (coordinate_replacement v i x).
    have hf : continuous f.
      move=> x; apply: (@continuous_comp T [the topologicalType of (I -> T)]
        (real_line_metric R) (fun y => coordinate_replacement v i y) F x).
      - exact: coordinate_replacement_continuous.
      - exact: hF.
    have hcq : closed [set r : real_line_metric R | r<=q] by exact: closed_le.
    have hc := (@continuous_closedP T (real_line_metric R) f).1 hf _ hcq.
    have hsub : A `<=` (f @^-1` [set r : real_line_metric R | r<=q]).
      move=> x hx; apply: (ih hs').
      + move=> j hj.
        have hji : j!=i by apply/eqP=> he; move: his; rewrite -he hj.
        rewrite /coordinate_replacement (negPf hji).
        apply: hvclos; by rewrite inE hj orbT.
      + move=> j hj; case: (eqVneq j i)=> [hji|hji].
        * by rewrite /coordinate_replacement hji eqxx.
        * rewrite /coordinate_replacement (negPf hji).
          apply: hvAout; by rewrite inE negb_or hji hj.
    have hvi : closure A (v i) by apply: hvclos; rewrite inE eqxx.
    have hh := hc _ (@closureS T A _ hsub (v i) hvi).
    change (is_true (F (coordinate_replacement v i (v i))<=q)) in hh.
    by rewrite coordinate_replacement_self in hh.
apply: (hstep (enum I) (enum_uniq I)).
- by move=> i _; exact: hp.
- by move=> i; rewrite mem_enum.
Qed.

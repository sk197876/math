(** Federer (1969), 2.9.24, p. 169: the step functions converge at every
    continuity point of f as the mesh tends to zero. The supporting finite
    geometry below finds the tag in the cell containing a given point. the
    continuity-point version suffices outside the countable BV discontinuity
    locus. The local Federer erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import StieltjesSums TaggedStepFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [tagged_step_function_nearby_sample]: supporting
    tag selection for the convergence assertion of Federer 2.9.24,
    p. 169. For an ordered odd tagged list of mesh below d,
    every point strictly after the left endpoint and at most the
    right endpoint receives a tag value within distance d. *)
Lemma tagged_step_function_nearby_sample (R : realType) (f : R -> R)
    (w : seq R) (d : R) : sorted <=%O w -> odd (size w) -> tagged_mesh_lt d w ->
  forall x : R, head 0 w<x -> x<=last 0 w ->
    exists r : R, r \in w /\ `|r-x|<d /\ tagged_step_function f w x=f r.
Proof.
have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|a [|r [|b rest]]] hsize hs ho hm x hax hxb.
- change (is_true (0<x)) in hax; change (is_true (x<=0)) in hxb; by lra.
- change (is_true (a<x)) in hax; change (is_true (x<=a)) in hxb; by lra.
- by move: ho; rewrite /=.
- have /andP[har /andP[hrb htail]] := hs.
  have /andP[hwidth hmesh] := hm.
  have hodd : odd (size (b::rest)) by move: ho; rewrite /= negbK.
  change (is_true (a<x)) in hax.
  change (is_true (x<=last 0 (b::rest))) in hxb.
  case: (boolP (a<x<=b))=> hcell.
  + have /andP[_ hxB] := hcell.
    exists r; split; first by rewrite !in_cons eqxx orbT.
    split.
    * rewrite ltr_norml; apply/andP; split; lra.
    * by rewrite tagged_step_function_cons hcell.
  + have hbx : b<x.
      rewrite ltNge; apply/negP=> hle.
      by move: hcell; rewrite hax hle.
    have hsmall : (size (b::rest)<n)%N by move: hsize; rewrite /= !ltnS; exact: ltnW.
    have [t [ht [hnear hvalue]]] := ih (b::rest) hsmall htail hodd hmesh x hbx hxb.
    exists t; split.
    * rewrite in_cons; apply/orP; right; rewrite in_cons; apply/orP; right; exact: ht.
    * split=> //; rewrite tagged_step_function_cons (negbTE hcell); exact: hvalue.
Qed.

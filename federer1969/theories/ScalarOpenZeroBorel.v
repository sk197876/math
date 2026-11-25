(** Federer (1969), 3.2.13, p. 250: measurable
    zero completion of the positive-domain Gamma integrand.
    This supporting topological lemma does not claim
    continuity of a negative power at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground BorelFunctionUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_open_zero_borel]: supporting
    measurability of the positive-ray integral defining
    Gamma in Federer 3.2.13, p. 250.
    A function continuous at each point of an open
    domain has a Borel zero completion, even when
    it has no finite limit at the domain boundary. *)
Lemma scalar_open_zero_borel (R:realType) (A:set (real_line_metric R)) (f:R->R):
  open A ->(forall a,A a ->
    (fun x:real_line_metric R=>(f x:real_line_metric R)) @ a -->(f a:real_line_metric R)) ->
  is_borel_function (fun x:real_line_metric R=>
    ((if asbool (A x) then f x else 0):real_line_metric R)).
Proof.
move=>hA hf U hU.
have hOpen:open [set x:real_line_metric R|A x /\U (f x)].
  rewrite openE=>x [hx hfx].
  have hAn:nbhs x A by apply:open_nbhs_nbhs; split.
  have hUn:nbhs (f x:real_line_metric R) U by apply:open_nbhs_nbhs; split.
  have hPre:=hf x hx U hUn.
  exact:filterI hAn hPre.
case:(pselect (U 0))=>h0.
- have hEq:(fun x:real_line_metric R=>((if asbool (A x) then f x else 0):real_line_metric R)) @^-1` U=
      [set x:real_line_metric R|A x /\U (f x)] `|` (~` A).
    apply/seteqP; split=>x /=.
    + case:asboolP=>hx hu; [left; by split|right; exact hx].
    + move=>[[hx hu]|hx].
      * case:asboolP=>ha; first exact hu.
        exfalso; exact:ha hx.
      * case:asboolP=>ha; last exact h0.
        exfalso; exact:hx ha.
  rewrite hEq; apply:(borel_family_binary_union (borel_sets_family [the topologicalType of real_line_metric R])).
  + exact:open_borel_set hOpen.
  + exact:closed_borel_set (open_closedC hA).
- have hEq:(fun x:real_line_metric R=>((if asbool (A x) then f x else 0):real_line_metric R)) @^-1` U=
      [set x:real_line_metric R|A x /\U (f x)].
    apply/seteqP; split=>x /=.
    + case:asboolP=>hx hu; first by split.
      exfalso; exact:h0 hu.
    + move=>[hx hu]; case:asboolP=>ha; first exact hu.
      exfalso; exact:ha hx.
  rewrite hEq; exact:open_borel_set hOpen.
Qed.

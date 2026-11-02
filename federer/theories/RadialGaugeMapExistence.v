(** Federer (1969), 3.2.35, p. 271:
    local existence of the corrected radial map,
    using the existing opaque source restriction.
    Apply erratum p. 5, book p. 271 line 24. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RadialGaugeMapUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_gauge_map_exists]: supporting
    existence of the corrected sphere parametrization
    in Federer 3.2.35, p. 271, with
    erratum p. 5, book p. 271 line 24.
    Restrict the displayed radial formula to exactly
    the actual unit sphere. Boundary equality and
    Lipschitz bounds are separate consequences under
    the original convex-body hypotheses. No selected
    global map or outside graph values are introduced. *)
Theorem radial_gauge_map_exists (R:realType) (V:lmodType R) (N:V->R) (g:V->R):
  exists f:partial_function V V,is_radial_gauge_map N g f.
Proof.
exists (partial_function_source_restrict [set x|N x= 1]
  (partial_function_total (fun x:V=>(g x)^-1*:x))).
constructor=>x y; rewrite partial_function_source_restrict_graph.
by [].
Qed.

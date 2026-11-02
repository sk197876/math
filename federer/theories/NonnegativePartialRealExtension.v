(** Federer (1969), 3.2.20, p. 257: an auxiliary
    everywhere-nonnegative total representative of the partial intrinsic
    Jacobian. Its existence uses only the existing opaque extension laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_partial_real_extension]: supporting
    auxiliary representative for the compact-chart sum in Federer
    3.2.20, p. 257. Every defined value is preserved
    exactly; no measurability hypothesis or globally selected new
    object is introduced, and the original partial domain is untouched. *)
Lemma nonnegative_partial_real_extension (R : realType) (X : Type)
    (d : partial_function X (real_line_metric R)) :
  (forall x j,partial_function_graph d x j -> 0<=j) ->
  exists J : X -> R,(forall x,0<=J x) /\ is_partial_function_total_extension d J.
Proof.
move=> hPos.
pose F := @PartialFunctionExtension.value X (real_line_metric R) d 0.
have hExt := @PartialFunctionExtension.laws X (real_line_metric R) d 0.
exists (fun x=>Num.max (F x) 0); split.
- by move=> x; rewrite le_max lexx orbT.
- move=> x j hj; have hF : F x=j := hExt x j hj.
  rewrite hF; exact: (max_idPl (hPos x j hj)).
Qed.

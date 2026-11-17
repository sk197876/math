(** Federer (1969), 3.4.8(10), p. 332:
    the actual increasingly ordered fibre
    points are continuous. Their proved
    local agreement with the continuous
    inverse branches supplies this conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground RelativeLocalInverseUP FiniteOrderedEnumeration
  OrderedFibreSequenceLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [ordered_fibre_branch_continuous_at]:
    continuity of psi_1,...,psi_nu on
    Y_nu, 3.4.8(10), p. 332.
    Only a valid original fibre index
    is used. The total representative's
    default value outside its actual domain
    has no role in the proof. *)
Theorem ordered_fibre_branch_continuous_at (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V C:set Y) (xi:X->R) (S:Y->seq X) (x0:X) (y:Y) j:
  continuous P ->continuous (fun x:X=>(xi x:real_line_metric R)) ->
  V y ->nbhs y V ->nbhs y C ->compact [set x|Z x /\C (P x)] ->
  (forall z,V z ->is_finite_ordered_enumeration [set x|Z x /\P x = z] xi (S z)) ->
  (forall x,Z x ->exists U W psi,is_relative_local_inverse P Z x U W psi) ->
  (j<size (S y))%N ->{for y,continuous (fun z:Y=>nth x0 (S z) j)}.
Proof.
move=>hP hXi hy hV hC hCompact hS hCharts hJ.
have [psi [hBase [hContinuous hNear]]]:=@ordered_fibre_sequence_local_agreement R X Y
  P Z V C xi S x0 y hP hXi hy hV hC hCompact hS hCharts.
pose i:'I_(size (S y)):=Ordinal hJ.
have hPoint:psi i y = nth x0 (S y) j:=hBase i.
have hEqualNear:nbhs y [set z|nth x0 (S z) j = psi i z].
  apply:filterS hNear=>z hz.
  change (nth x0 (S z) j = psi i z).
  rewrite hz (nth_map i) ?size_enum_ord //.
  have hIndex:nth i (enum 'I_(size (S y))) j = i:=@nth_ord_enum (size (S y)) i i.
  by rewrite hIndex.
move=>W hW.
have hPsiW:nbhs (psi i y) W by rewrite hPoint;exact:hW.
have hPre:nbhs y (psi i @^-1` W):=hContinuous i W hPsiW.
apply:filterS (filterI hEqualNear hPre)=>z [hEqual hz].
change (W (nth x0 (S z) j)).
by rewrite hEqual.
Qed.

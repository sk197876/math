(** Federer (1969), 3.4.8(10), p. 332:
    the selected increasing fibre sequences
    agree near each base point with
    the actual continuous local inverse branches.
    Uniqueness of the independent order laws
    identifies the two selections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground RelativeLocalInverseUP FiniteFibreEnumerationUP
  FiniteOrderedEnumeration OrderedFibreSequences FiniteLocalInverseBranchAssembly FiniteOrderedBranchNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ordered_fibre_sequence_local_agreement]:
    the increasing fibre points psi_lambda
    are locally the same as the
    continuous inverse branches, 3.4.8(10),
    p. 332. The original ordered
    laws supply uniqueness; compactness supplies
    completeness of the nearby branch family. *)
Theorem ordered_fibre_sequence_local_agreement (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V C:set Y) (xi:X->R) (S:Y->seq X) (x0:X) (y:Y):
  continuous P ->continuous (fun x:X=>(xi x:real_line_metric R)) ->
  V y ->nbhs y V ->nbhs y C ->compact [set x|Z x /\C (P x)] ->
  (forall z,V z ->is_finite_ordered_enumeration [set x|Z x /\P x = z] xi (S z)) ->
  (forall x,Z x ->exists U W psi,is_relative_local_inverse P Z x U W psi) ->
  exists psi:'I_(size (S y))->Y->X,
    (forall i,psi i y = nth x0 (S y) (i:nat)) /\
    (forall i,{for y,continuous (psi i)}) /\
    nbhs y [set z|S z = map (fun i=>psi i z) (enum 'I_(size (S y)))].
Proof.
move=>hP hXi hy hV hC hCompact hS hCharts.
have hAt:=hS y hy.
pose nu:=size (S y).
pose a:=fun i:'I_nu=>nth x0 (S y) (i:nat).
have hEnumeration:=@ordered_sequence_fibre_enumeration R [the choiceType of (X:Type)] Y
  P Z y xi x0 (S y) hAt.
have [psi [hBase [hContinuous hNear]]]:=@finite_local_inverse_branch_assembly R X Y [the finType of 'I_nu]
  P Z C y a hP hC hCompact hEnumeration hCharts.
have hTrans:transitive (fun x z:X=>xi x<xi z) by move=>x z w;exact:lt_trans.
have hOrder (i j:'I_nu):(i<j)%N ->xi (psi i y)<xi (psi j y).
  move=>hIJ;rewrite !hBase /a.
  exact:(@sorted_ltn_nth (X:Type) (fun x z=>xi x<xi z) hTrans x0 (S y) hAt.2
    (i:nat) (j:nat) (ltn_ord i) (ltn_ord j) hIJ).
have hOrderedNear:=@finite_ordered_branch_neighbourhood R X Y nu xi psi y hXi hContinuous hOrder.
exists psi;split;first exact:hBase.
split;first exact:hContinuous.
apply:filterS (filterI hV (filterI hNear hOrderedNear))=>z [hzV [hzEnumeration hzSorted]].
have hOther:is_finite_ordered_enumeration [set x|Z x /\P x = z] xi
    (map (fun i=>psi i z) (enum 'I_nu)).
  split;last exact:hzSorted.
  move=>x;split.
  - move=>/mapP[i _ hEqual];rewrite hEqual;exact:hzEnumeration.1 i.
  - move=>[hx hPx];have [i hi]:=hzEnumeration.2.1 x hx hPx.
    apply/mapP;exists i;first by rewrite mem_enum.
    exact:esym hi.
exact:(@finite_ordered_enumeration_unique R [the choiceType of (X:Type)]
  [set x|Z x /\P x = z] xi (S z) _ (hS z hzV) hOther).
Qed.

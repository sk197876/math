(** Federer (1969), 3.4.8(10), p. 332:
    the original strict order is retained
    by finitely many continuous local branches.
    Apply the existing finite-filter intersection
    and strict scalar-order neighbourhood laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground ContinuousStrictOrderNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ordered_branch_neighbourhood]:
    the local branches keep the ordering
    by omega_(m+1) used to characterize
    psi_lambda in 3.4.8(10), p. 332.
    This statement retains empty and singleton
    branch families. *)
Theorem finite_ordered_branch_neighbourhood (R:realType) (X Y:topologicalType)
    nu (xi:X->R) (psi:'I_nu->Y->X) (y:Y):
  continuous (fun x:X=>(xi x:real_line_metric R)) ->
  (forall i,{for y,continuous (psi i)}) ->
  (forall i j:'I_nu,(i<j)%N ->xi (psi i y)<xi (psi j y)) ->
  nbhs y [set z|sorted (fun x t=>xi x<xi t) (map (fun i=>psi i z) (enum 'I_nu))].
Proof.
move=>hXi hPsi hOrder.
pose index:finType:=[the finType of ('I_nu*'I_nu)%type].
pose H:=fun q:index=>[set z| (q.1<q.2)%N ->xi (psi q.1 z)<xi (psi q.2 z)].
have hEach (q:index):nbhs y (H q).
  case:(ltnP q.1 q.2)=>[hLess|hNotLess].
  - have hFirst:=continuous_comp (hPsi q.1) (hXi (psi q.1 y)).
    have hSecond:=continuous_comp (hPsi q.2) (hXi (psi q.2 y)).
    have hNear:=@continuous_strict_order_neighbourhood R Y
      (fun z=>xi (psi q.1 z)) (fun z=>xi (psi q.2 z)) y hFirst hSecond (hOrder q.1 q.2 hLess).
    by apply:filterS hNear=>z hz _.
  - have hTrivial:nbhs y (@setT Y):=@filterT Y (nbhs y) (nbhs_filter y).
    apply:filterS hTrivial=>z _ hLess.
    have hBad:=leq_ltn_trans hNotLess hLess;by rewrite ltnn in hBad.
have hAll:=@filter_forall Y index H (nbhs y) (nbhs_filter y) hEach.
have hEnum:sorted (fun i j:'I_nu=>(i<j)%N) (enum 'I_nu).
  change (is_true (sorted (relpre (fun i:'I_nu=>(i:nat)) ltn) (enum 'I_nu))).
  by rewrite -sorted_map val_enum_ord iota_ltn_sorted.
apply:filterS hAll=>z hz.
apply:(homo_sorted _ (enum 'I_nu) hEnum)=>i j hLess.
exact:hz (i,j) hLess.
Qed.

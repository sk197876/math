(** Federer (1969), 3.3.1, p. 287: the kernel map is
    equivariant for the original orthogonal actions. This algebraic
    fact supplies the continuous open map and invariant-measure
    assertion through 2.7.1 and 2.7.16(6). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import ModuleQuotient Hom GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct FiniteCoordinates InnerProductUP InnerMetric HomInner HomSpaceTopology
  LinearGroupSealed LinearGroupTopology IsotropyGroupTopology OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace
  GrassmannHomogeneousSpace StructureProjectionKernelUP StructureProjectionKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section KernelAction.
Variable R:realType.
Variables n m:nat.
Hypothesis hmn:(m<=n)%N.
Local Notation hN:=(@euclidean_inner_productP R n).
Local Notation hM:=(@euclidean_inner_productP R m).
Local Notation hK:=(@euclidean_inner_productP R (n-m)).
Local Notation hbn:=(@coordinate_basisP R n).
Local Notation hbk:=(@coordinate_basisP R (n-m)).
Local Notation O:=(euclidean_orthogonal_group R n).
Local Notation om:=(@orthogonal_element_map R (R_n R n)
  (@euclidean_inner_product R n) hN n (@coordinate_basis R n) hbn).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hN hbn)
  (linear_group_inv hN hbn) (linear_group_unit hN hbn) O mulS invS eS.
Local Notation AP:=(orthogonal_projection_action hM hN hbn hS).
Local Notation AG:=(grassmann_action hK hN hbk hbn).

(** Source for [structure_projection_kernel_equivariant]:
    supporting the final sentence of Federer 3.3.1, p. 287:
    ker(p composed with g inverse)=g[ker p]. The equality
    concerns the actual planes and holds on every vector. *)
Theorem structure_projection_kernel_equivariant (g:O)
    (p:euclidean_projection_space R n m):
  structure_projection_kernel hmn (AP g p)=
    AG g (structure_projection_kernel hmn p).
Proof.
have [hLeft hRight]:=orthogonal_element_inv hS g.
apply:grassmann_ext=>x.
rewrite structure_projection_kernelE grassmann_actionE.
change (orthogonal_projection_map (AP g p) x=0 <->
  exists2 w,grassmann_val (structure_projection_kernel hmn p) w & om g w=x).
rewrite orthogonal_projection_actionE; split.
- move=>hx; exists (om (invS g) x); last exact:(hRight x).
  apply/(structure_projection_kernelE hmn p (om (invS g) x)); exact:hx.
- move=>[w hw <-]; rewrite hLeft.
  exact:((structure_projection_kernelE hmn p w).1 hw).
Qed.
End KernelAction.

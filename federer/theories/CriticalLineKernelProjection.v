(** Federer (1969), 3.4.2(7), p. 314: choose an orthogonal
    projection whose kernel is the line through the nonzero direction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates LinearBasis
  LinearRangeBasis EuclideanProjectionSpace StructureProjectionKernel StructureKernelOnto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_line_kernel_projection_exists]: the
    choice ker q={t p(z):t in R} in 3.4.2(7), p. 314. A nonzero
    vector gives an actual one-dimensional range basis; the proved
    Grassmann kernel parametrisation gives q. The one-dimensional
    source and zero-dimensional target are included. *)
Theorem critical_line_kernel_projection_exists (R:realType) k (v:R_n R k.+1):
  v!=0 ->exists q:euclidean_projection_space R k.+1 k,
    forall w,euclidean_projection_linear q w=0 <->exists t:R,w=t*:v.
Proof.
move=>hv.
pose X:=R_n R k.+1.
have hLinear:linear (fun x:R_n R 1=>x ord0*:v).
  move=>a x y.
  by rewrite !ffunE scalerDl scalerA.
pose L:Hom (R_n R 1) X:=@HomMap R (R_n R 1) X (fun x=>x ord0*:v)
  (introT (asboolP _) hLinear).
have hInjective:injective (hom_as_linear L).
  move=>x y hEqual.
  change (x ord0*:v=y ord0*:v) in hEqual.
  have hZero:(x ord0-y ord0)*:v=0 by rewrite scalerBl hEqual subrr.
  have hCoe:x ord0=y ord0.
    apply/eqP;move/eqP:hZero;by rewrite scaler_eq0 (negbTE hv) orbF subr_eq0.
  apply/ffunP=>i;by rewrite (ord1 i) hCoe.
have [b hb]:=@injective_range_basis_exists R (R_n R 1) X (hom_as_linear L)
  hInjective 1 (@coordinate_basis R 1) (@coordinate_basisP R 1).
pose K1:=@GrassmannSubspace R X 1 (range_subspace (hom_as_linear L)) (ex_intro _ b hb).
have hDimension:(k.+1-k)%N= 1%N by rewrite subSnn.
have [K hK]:exists K:G X (k.+1-k),forall w,grassmann_val K w <->exists t:R,w=t*:v.
  rewrite hDimension;exists K1;move=>w;split.
  - move=>[x hx];exists (x ord0);exact:hx.
  - move=>[t ht];exists [ffun i:'I_1=>t].
    change (w=[ffun i:'I_1=>t] ord0*:v).
    by rewrite ffunE -ht.
have hLe:(k<=k.+1)%N:=leqnSn k.
have [q hq]:=structure_projection_kernel_onto hLe K.
exists q;move=>w.
rewrite -(structure_projection_kernelE hLe q w) hq.
exact:hK.
Qed.

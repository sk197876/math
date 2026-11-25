(** Federer (1969), 3.4.2(7), p. 312: the base case mu=nu>0.
    Equality of the kernel and Z excludes distinct source pairs in a fibre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates LinearRankUP FiniteSourceLinearRank
  EuclideanProjectionSpace StructureProjectionKernel GrassmannDimensionInclusion
  EuclideanInnerProduct InnerNorm ExtendedSupremumUP CriticalManifoldFamilyUP
  CriticalManifoldChartLaws CriticalOscillationUP CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_subspace_dimension_bound]: the fixed subspace
    Z in 3.4.2(2), p. 310, has dimension at most m. This supporting
    basis argument makes nu=m-d a genuine nonnegative codimension. *)
Lemma critical_subspace_dimension_bound (R:realType) m d (Z:G (R_n R m) d):
  (d<=m)%N.
Proof.
have [b hb]:=grassmann_proof Z.
pose L:=hom_of_linear (subspace_inclusion (grassmann_val Z)).
have hRank:=@finite_source_injective_linear_rank R
  (subspace_space (grassmann_val Z)) (R_n R m) L d b hb
  (@subspace_val_injective R (R_n R m) (grassmann_val Z)).
exact:(@linear_rank_codomain_bound R (subspace_space (grassmann_val Z))
  (R_n R m) L m (@coordinate_basis R m) (@coordinate_basisP R m) d hRank).
Qed.

(** Source for [critical_codimension_chart_kernel]: ker p=Z in the
    mu=nu case of the proof of 3.4.2(7), p. 312. Both subspaces have
    actual dimension m-nu=d, and the chart supplies their inclusion. *)
Lemma critical_codimension_chart_kernel (R:realType) m d k
    (Z:G (R_n R m) d) (S:set (R_n R m))
    (p:euclidean_projection_space R m (m-d)) g:
  is_critical_manifold_chart k (grassmann_val Z) S p g ->
  forall x,grassmann_val Z x <->euclidean_projection_linear p x=0.
Proof.
move=>h.
have hd:=critical_subspace_dimension_bound Z.
have hex:exists K:G (R_n R m) (m-(m-d)),
    forall x,grassmann_val K x <->euclidean_projection_linear p x=0.
  exists (structure_projection_kernel (leq_subr d m) p).
  exact:structure_projection_kernelE.
rewrite (subKn hd) in hex.
have [K hK]:=hex.
have hIn x (hx:grassmann_val K x):grassmann_val Z x.
  exact:(critical_chart_kernel h ((hK x).1 hx)).
have hEq:=grassmann_equal_dimension_inclusion hIn.
move=>x;split.
- move=>hx;exact:((hK x).1 ((hEq x).2 hx)).
- move=>hx;exact:(critical_chart_kernel h hx).
Qed.

(** Source for [critical_codimension_eta_zero]: η vanishes in the
    projection-chart case mu=nu, in the proof of 3.4.2(7), p. 312.
    Univalence and ker p=Z exclude every distinct original test pair.
    This conclusion holds for any function and every cutoff. *)
Lemma critical_codimension_eta_zero (R:realType) m d k (Y:lmodType R)
    (NY:Y->R) (Z:G (R_n R m) d) (S C:set (R_n R m))
    (p:euclidean_projection_space R m (m-d)) g (f:R_n R m->Y) lambda delta:
  is_critical_manifold_chart k (grassmann_val Z) S p g ->C `<=` S ->
  critical_eta NY (grassmann_val Z) S C f lambda delta=0%E.
Proof.
move=>h hCS;apply/eqP;rewrite eq_le;apply/andP;split;last exact:critical_eta_nonnegative.
apply:(extended_supremum_least (critical_eta_laws NY (grassmann_val Z) S C f lambda delta)).
move=>q [->|[x [c [hx [hc [hZ [/andP[hp _] hq]]]]]]];first exact:lexx.
have hZero:euclidean_projection_linear p (x-c)=0.
  exact:((critical_codimension_chart_kernel h (x-c)).1 hZ).
have hProj:euclidean_projection_linear p x=euclidean_projection_linear p c.
  by apply/eqP;rewrite -subr_eq0 -linearB hZero eqxx.
have he:x=c:=critical_chart_projection_injective h hx (hCS c hc) hProj.
by rewrite he subrr inner_norm0 ltxx in hp.
Qed.

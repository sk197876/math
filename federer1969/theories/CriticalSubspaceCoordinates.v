(** Federer (1969), 3.4.2(7), p. 313: an orthonormal basis of
    the fixed subspace supplies bounded unit-vector coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerProductRestriction InnerNorm
  OrthonormalFamilies OrthonormalisationUP GramSchmidt InnerNormalization
  OrthonormalParseval Annihilator LinearBasis FiniteDualDimension InnerNormInequalities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_subspace_unit_coordinates]: the choice of
    e_1,...,e_(m-nu) and the bounds |z dot e_i|<=1 in 3.4.2(7),
    p. 313. The actual basis of Z gives its orthonormal basis by
    1.7.1. Cauchy's inequality bounds every unit-vector coefficient.
    Dimension zero is retained, with an empty family. *)
Theorem critical_subspace_unit_coordinates (R:realType) m d (Z:G (R_n R m) d):
  exists e:'I_d->R_n R m,
    (forall i,grassmann_val Z (e i)) /\
    (forall i,inner_norm (@euclidean_inner_productP R m) (e i)= 1) /\
    forall z,grassmann_val Z z ->inner_norm (@euclidean_inner_productP R m) z<=1 ->
      exists a:'I_d->R,(forall i,`|a i|<=1) /\z=\sum_i a i*:e i.
Proof.
pose X:=R_n R m.
pose B:=@euclidean_inner_product R m.
pose hB:=@euclidean_inner_productP R m.
pose V:=subspace_space (grassmann_val Z).
pose C:=@restricted_inner_product R X B (grassmann_val Z).
pose hC:=@restricted_inner_productP R X B hB (grassmann_val Z).
have [b hb]:=grassmann_proof Z.
have [E [hE hOrtho]]:=@orthonormal_basis_exists R V C hC d b hb.
have hEO:=orthonormalisation_orthonormal hOrtho.
pose e i:=subspace_val (E i).
have hAmbient:orthonormal_family B e:=hEO.
have hNorm i:inner_norm hB (e i)= 1:=orthonormal_norm1 hB hAmbient i.
exists e;split;first by move=>i;exact:subspace_valP.
split;first exact:hNorm.
move=>z hz hUnit.
pose v:=subspace_lift hz.
pose a i:=dual_basis hE i v.
have hExpansion:z=\sum_i a i*:e i.
  have h:=congr1 (@subspace_val R X (grassmann_val Z)) (basis_vector_expansion hE v).
  by rewrite subspace_liftE linear_sum in h.
exists a;split;last exact:hExpansion.
move=>i.
have hCoordinate:a i=B z (e i).
  have h:=@orthonormal_basis_inner_coordinate R V C hC (Finite.clone 'I_d _) E hEO hE i v.
  exact:h.
have hBound:=inner_cauchy hB z (e i).
rewrite (hNorm i) mulr1 in hBound.
rewrite hCoordinate;exact:(le_trans hBound hUnit).
Qed.

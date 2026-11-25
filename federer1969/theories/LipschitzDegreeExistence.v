(** Federer (1969), 4.1.26, p. 383:
    the original finite signed numerical fibre
    sum defines a partial real function.
    This set-theoretic existence proof does not
    claim its later almost-everywhere domain or
    the current-image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialFibreNumericalSum LipschitzDegreeSummandSealed LipschitzDegreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [lipschitz_degree_exists]: the original
    degree graph in 4.1.26, p. 383,
    is single valued by the previously proved
    signed numerical-sum laws. No existence of
    a value at every target point is assumed. *)
Theorem lipschitz_degree_exists (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m)):
  exists d:partial_function (R_n R m) R,is_lipschitz_degree f A d.
Proof.
pose S:=partial_fibre_numerical_sum f (partial_function_postcompose
  (@LipschitzDegreeSummand.value R m f A) (fun s:R=>(s%:E:extended_real_line R))).
have hUnique y (a b:R):partial_function_graph S y a%:E->
    partial_function_graph S y b%:E->a=b.
  move=>hA hB;exact:EFin_inj (partial_function_single_valued hA hB).
exists (@Build_partial_function (R_n R m) R
  (fun y a=>partial_function_graph S y a%:E) hUnique).
by move=>y a;split.
Qed.

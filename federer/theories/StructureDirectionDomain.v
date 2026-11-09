(** Federer (1969), 3.3.4, pp. 290–291:
    the actual partial direction-map domain is
    Borel; the zero projection is excluded
    before any unit direction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  BorelFunctionUP BorelFunctionBasic TopologicalBorel FiniteExceptionalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_direction_domain_borel]:
    Borelness of domain(w composed with q),
    used for R_v in Federer 3.3.4,
    p. 291. For an actual Borel q,
    the nonzero-norm domain is exactly the
    inverse image of the complement of the
    closed zero singleton. *)
Theorem structure_projective_direction_domain_borel (R:realType) (X:topologicalType)
    m (q:X->inner_metric_space (@euclidean_inner_productP R m.+1)):
  is_borel_function q ->
  borel_set [set x|0<inner_norm (@euclidean_inner_productP R m.+1) (q x)].
Proof.
move=>hQ.
pose E:=inner_metric_space (@euclidean_inner_productP R m.+1).
have hZero:@borel_set E [set (0:E)].
  exact:(@finite_metric_set_borel R E [set (0:E)] (finite_set1 (0:E))).
have hRaw:=borel_function_preimage hQ (borel_set_complement hZero).
have hEq:[set x|0<inner_norm (@euclidean_inner_productP R m.+1) (q x)]=
    q @^-1` (~` [set (0:E)]).
  apply/seteqP; split=>x.
  - change (0<inner_norm (@euclidean_inner_productP R m.+1) (q x) ->~(q x=0)).
    by rewrite inner_norm_gt0; move=>/eqP hx.
  - change (~(q x=0) ->0<inner_norm (@euclidean_inner_productP R m.+1) (q x)).
    move=>hx; rewrite inner_norm_gt0; by apply/eqP.
by rewrite hEq.
Qed.

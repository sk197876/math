(** Federer (1969), 4.1.26, pp. 383–384:
    exact empty-fibre and injective-linear computations
    of the original signed degree. These
    supporting laws check both orientation signs
    and the nonzero empty-dimensional orientation
    without choosing a value at undefined sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  PartialFunctionUP NumericalSum NumericalSumSingleSupport
  LipschitzDegreeSealed LipschitzDegreeFibreGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_outside_image]: the
    original fibre formula of 4.1.26, p. 383,
    has value zero at every point
    outside f(A), without a differentiability
    hypothesis on f outside A. *)
Theorem lipschitz_degree_outside_image (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m)) y:
  ~(f @` A) y->partial_function_graph (@LipschitzDegree.value R m f A) y 0.
Proof.
move=>hOutside;apply:(@lipschitz_degree_fibre_graph R m f A y 0).2.
exists (fun _=>0:R);split.
- move=>x hx hxy;exfalso;apply:hOutside;by exists x.
- have hEmpty:A `&` [set x|f x=y]=set0.
    apply/seteqP;split;last by [].
    move=>x [hx hxy];exfalso;apply:hOutside;by exists x.
  by rewrite hEmpty numerical_sum_empty.
Qed.

(** Source for [lipschitz_degree_injective_linear_value]:
    the determinant-sign specialization of the
    original fibre formula in 4.1.26, p. 383,
    for a bounded injective linear map.
    The proof uses only the existing
    differential and numerical-sum laws. *)
Theorem lipschitz_degree_injective_linear_value (R:realType) m
    (L:Hom (R_n R m) (R_n R m))
    (hBound:norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R m)) L)
    (hInjective:injective L) (A:set (R_n R m)) x:
  A x->partial_function_graph (@LipschitzDegree.value R m L A) (L x)
    (Num.sg (@euclidean_det R m (hom_as_linear L))).
Proof.
move=>hx.
pose s:=Num.sg (@euclidean_det R m (hom_as_linear L)).
apply:(@lipschitz_degree_fibre_graph R m L A (L x) s).2.
exists (fun _=>s);split.
- move=>z _ _;exists L;split;last reflexivity.
  exact:(@norm_differential_linear R (R_n R m) (R_n R m)
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True) z L
    (norm_full_domain_interior _ z) hBound).
- apply:(@numerical_sum_single_support R (R_n R m)
    (A `&` [set z|L z=L x]) (fun _=>s%:E) x (conj hx (erefl _))).
  move=>z [_ hz] hNot.
  have hEqual:z=x:=@hInjective z x hz.
  by rewrite hEqual eqxx in hNot.
Qed.

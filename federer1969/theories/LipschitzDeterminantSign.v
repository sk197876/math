(** Federer (1969), 4.1.26, pp. 383–384:
    sign det Df is the determinant-sign
    postcomposition of the original partial differential.
    Under injectivity on A, its value at
    a point of A is exactly the
    signed degree at that point's image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSealed
  NormDifferentialDirectional InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanLinearMaps PartialFunctionUP PartialFunctionPostcomposition
  NumericalSumSingleSupport LipschitzDegreeSealed LipschitzDegreeFibreGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_determinant_sign]: the original
    partial sign det Df in the last
    sentence of 4.1.26, p. 384. This
    abbreviates the old opaque differential and
    ordinary postcomposition; no value is assigned
    where that differential is undefined. *)
Definition lipschitz_determinant_sign (R:realType) m (f:R_n R m->R_n R m):
    partial_function (R_n R m) R:=
  partial_function_postcompose
    (@NormDifferential.value R (R_n R m) (R_n R m)
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True) f)
    (fun D=>Num.sg (@euclidean_det R m (hom_as_linear D))).

(** Source for [lipschitz_degree_injective_fibre]:
    the univalent-fibre step used in the
    final assertion of 4.1.26, p. 384.
    Injectivity is required only on A,
    not on the whole source. The
    original finite degree graph supplies the
    differential at the point in that fibre. *)
Theorem lipschitz_degree_injective_fibre (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m)) x c:
  {in A &,injective f}->A x->
  partial_function_graph (@LipschitzDegree.value R m f A) (f x) c->
  partial_function_graph (@lipschitz_determinant_sign R m f) x c.
Proof.
move=>hInjective hx hDegree.
have[w [hOn hSum]]:=(@lipschitz_degree_fibre_graph R m f A (f x) c).1 hDegree.
have hPoint:(A `&` [set z|f z=f x]) x:=conj hx (erefl _).
have hOff:forall z,(A `&` [set z|f z=f x]) z->z!=x->(w z)%:E=0%E.
  move=>z [hz hImage] hNot.
  have hEqual:z=x:=hInjective z x (mem_set hz) (mem_set hx) hImage.
  by rewrite hEqual eqxx in hNot.
have hSingle:=@numerical_sum_single_support R (R_n R m)
  (A `&` [set z|f z=f x]) (fun z=>(w z)%:E) x hPoint hOff.
have hValue:w x=c.
  apply:EFin_inj;move:hSum;rewrite hSingle;by move=>[->].
have[D [hD hSign]]:=hOn x hx (erefl _).
exists D;split.
- exact:(@NormDifferential.laws R (R_n R m) (R_n R m)
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True) f x D).2 hD.
- exact:eq_trans hSign hValue.
Qed.

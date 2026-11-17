(** Federer (1969), 3.4.8(11), p. 333:
    the squared norm in the barrier
    Psi is analytic. Reuse coordinate analyticity,
    finite scalar sums and the original
    Euclidean inner-product identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP NormAnalyticOperations NormAnalyticScalarProducts
  NormOpenDomainLaws EuclideanScalarCoordinateAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_squared_norm_analytic]:
    analyticity of the actual |y| squared
    used in Psi, 3.4.8(11), p. 333.
    This supporting lemma includes dimension zero. *)
Lemma euclidean_squared_norm_analytic (R:realType) n:
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun z:R^o=>`|z|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) setT
    (fun x=>(inner_norm (@euclidean_inner_productP R n) x)^+2).
Proof.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hSquares i:=@norm_analytic_scalar_power R (R_n R n) NX hNX setT
  (fun x=>x i) 2%N (@euclidean_scalar_coordinate_analytic R n i).
have hSum:=@norm_analytic_finite_scalar_sum R (R_n R n) NX hNX setT
  (Finite.clone 'I_n _) (fun i x=>(x i)^+2)
  (fun x _=>norm_full_domain_interior NX x) hSquares.
apply:(@norm_analytic_domain_agreement R (R_n R n) R^o NX (fun z:R^o=>`|z|)
  hNX (@scalar_absolute_value_norm R) setT (fun x=>\sum_(i<n) (x i)^+2)
  (fun x=>NX x ^+2) _ hSum)=>x _.
rewrite /NX inner_norm_sqr /euclidean_inner_product.
apply:eq_bigr=>i _;exact:expr2.
Qed.

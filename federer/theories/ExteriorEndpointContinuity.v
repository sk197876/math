(** Supporting continuity for the compact and open covering alternatives in
    Federer (1969), 2.10.3, p. 172. The finite endpoint map is polynomial;
    use the existing coordinate proof of continuity of the exterior product
    and the actual induced norm. its algebra background is cited separately
    in ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates CoordinateProjection
  InnerNorm InnerMetric InnerNormedTopology InnerExteriorPositivity ExteriorNorm ExteriorGrading
  FiniteExteriorPowers ExteriorProductContinuity EuclideanCoordinateTopology
  OrthonormalFamilies ExteriorEndpointAffinity ExteriorDiameterUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [paired_exterior_norm]: supporting real-valued
    endpoint form of the exterior-product norm in Federer
    2.10.3, pp. 171–172. The pair index records both
    endpoints of each vector difference. *)
Definition paired_exterior_norm (R : realType) (n m : nat)
    (p : ('I_m*bool)%type -> R_n R n) : R :=
  @exterior_norm R (real_exterior_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
    (paired_exterior_product p).

(** Source for [paired_exterior_normE]: supporting evaluation
    of the paired notation as the printed difference
    product of Federer 2.10.3, p. 171. *)
Lemma paired_exterior_normE (R : realType) (n m : nat)
    (p : ('I_m*bool)%type -> R_n R n) :
  paired_exterior_norm p=exterior_difference_norm (fun i => p (i,false)) (fun i => p (i,true)).
Proof. by []. Qed.

(** Source for [paired_exterior_norm_continuous]: supporting
    joint endpoint continuity for the alternatives in
    Federer 2.10.3, p. 172. Finite coordinate expansion
    of the exterior product proves continuity; the
    target norm is exactly the norm induced in 1.7.5,
    p. 32. Degree zero is also continuous as an
    intermediate boundary case. *)
Theorem paired_exterior_norm_continuous (R : realType) (n m : nat) :
  continuous (fun p : ('I_m*bool)%type -> inner_metric_space (@euclidean_inner_productP R n) =>
    (paired_exterior_norm p : real_line_metric R)).
Proof.
pose M := inner_metric_space (@euclidean_inner_productP R n).
pose E := inner_metric_space (@exterior_inner_productP R (real_exterior_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
have hd : continuous (fun p : ('I_m*bool)%type -> M =>
    (fun i : 'I_m => (p (i,false)-p (i,true) : M))).
  apply: (@coordinate_family_continuous [the topologicalType of (('I_m*bool)%type -> M)]
    [the eqType of 'I_m] (fun _ => [the topologicalType of M])
    (fun i p => (p (i,false)-p (i,true) : M))).
  move=> i p; apply: continuousB; exact: proj_continuous.
have ho : orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hprod := @exterior_product_continuous_orthonormal R (real_exterior_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) ho m.
have hp : continuous (fun p : ('I_m*bool)%type -> M => (paired_exterior_product p : E)).
  move=> p; exact: continuous_comp (hd p) (hprod (fun i => p (i,false)-p (i,true))).
have hn : continuous (fun x : E =>
    (@exterior_norm R (real_exterior_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m x : real_line_metric R)).
  have he : (fun x : E => `|x|)=@exterior_norm R (real_exterior_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
    by apply: funext=> x; rewrite inner_norm_topologyE.
  rewrite -he; exact: norm_continuous.
move=> p; exact: continuous_comp (hp p) (hn (paired_exterior_product p)).
Qed.

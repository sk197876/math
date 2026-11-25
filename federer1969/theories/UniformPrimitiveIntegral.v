(** Supporting elementary-calculus proof for Federer (1969), 2.6.3(2), pp.
    117–118, using the already proved Riemann-Stieltjes sums of 2.5.17, pp.
    110–111. This sufficient finite-increment criterion is proved here; no
    external calculus theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology normedtype lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength StieltjesSums StieltjesIntegral
  StieltjesMonotone UniformPrimitiveUP TaggedPrimitiveEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [uniform_primitive_riemann_integral]: supporting
    fundamental-theorem evaluation used by Federer 2.6.3(2), pp. 117–118
    Uniform first-order increments telescope in the defining Riemann sums,
    giving the primitive difference. The statement includes a=b and retains
    explicit continuity of the integrand. *)
Theorem uniform_primitive_riemann_integral (R : realType) (f F : R -> R) (a b : R) :
  continuous f -> a <= b -> is_uniform_primitive_on f F a b ->
  F b-F a = stieltjes_integral (fun x => x) f a b.
Proof.
move=> hf hab hF.
have hg : curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
  apply: monotone_locally_finite_variation; by move=> x y h.
apply: (stieltjes_integral_unique hg hf hab)=> e he.
have hlen : 0 < b-a+1 by lra.
pose eps := e/(b-a+1).
have heps : 0 < eps by rewrite /eps divr_gt0.
have [d [hd hcell]] := hF eps heps.
exists d; split=> // w hw hmesh.
have hbnd := @tagged_primitive_error_bound R f F a b d eps w hw hmesh hcell.
apply: le_lt_trans hbnd _.
have hgap : b-a < b-a+1 by lra.
have hmul : eps*(b-a) < eps*(b-a+1) by rewrite ltr_pM2l.
by rewrite /eps divfK ?gt_eqF // in hmul.
Qed.

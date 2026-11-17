(** Federer (1969), 3.4.10, p. 338:
    the surface cited to Bruhat and Whitney,
    section 11(c), p. 159, is an
    actual globally defined analytic variety. Reuse
    the proved analytic coordinate and scalar operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormAnalyticUP NormAnalyticOperations
  NormAnalyticScalarProducts EuclideanScalarCoordinateAnalytic FiniteAnalyticVarietyUP
  AnalyticVarietyGermUP BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SurfaceAnalytic.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation hB:=(@euclidean_inner_productP R 3).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).

(** Source for [bruhat_whitney_surface_equation]: the
    exact polynomial in Bruhat and Whitney,
    section 11(c), p. 159, cited in
    3.4.10, p. 338. *)
Definition bruhat_whitney_surface_equation (v:X):R:=
  v (Ordinal (isT:(1<3)%N))*v ord_max*
    ((v ord0)^+2-v ord_max*(v (Ordinal (isT:(1<3)%N)))^+2)+(v ord0)^+4.

(** Source for [bruhat_whitney_surface_equation_analytic]: analyticity
    of the original displayed polynomial, supporting
    the cited example in 3.4.10, p. 338. *)
Lemma bruhat_whitney_surface_equation_analytic:
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT bruhat_whitney_surface_equation.
Proof.
have hX:=@euclidean_scalar_coordinate_analytic R 3 ord0.
have hY:=@euclidean_scalar_coordinate_analytic R 3 (Ordinal (isT:(1<3)%N)).
have hZ:=@euclidean_scalar_coordinate_analytic R 3 ord_max.
exact:(norm_analytic_add
  (norm_analytic_scalar_product (norm_analytic_scalar_product hY hZ)
    (norm_analytic_subtract (norm_analytic_scalar_power 2%N hX)
      (norm_analytic_scalar_product hZ (norm_analytic_scalar_power 2%N hY))))
  (norm_analytic_scalar_power 4%N hX)).
Qed.

(** Source for [bruhat_whitney_surface_finite_variety]: the
    cited example in 3.4.10, p. 338,
    is a genuine finite analytic variety on
    the whole original ambient space. *)
Theorem bruhat_whitney_surface_finite_variety:
  @is_finite_analytic_variety R X NX hNX setT (@BruhatWhitneySurface.set R).
Proof.
split;first exact:openT.
exists (Finite.clone unit _),(fun _=>bruhat_whitney_surface_equation);split.
- by move=>i;exact:bruhat_whitney_surface_equation_analytic.
- move=>v;split.
  + move/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R))=>h.
    split;first exact:Logic.I.
    by move=>i.
  + move=>[_ h];apply/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R)).
    exact:h tt.
Qed.

(** Source for [bruhat_whitney_surface_locally_analytic]: the
    original analytic-set hypothesis holds at every
    centre for the example in 3.4.10, p. 338. *)
Theorem bruhat_whitney_surface_locally_analytic:
  @is_analytic_set_in R X NX hNX setT (@BruhatWhitneySurface.set R).
Proof.
move=>a _;exists setT,(@BruhatWhitneySurface.set R);split;first exact:Logic.I.
split;[exact:bruhat_whitney_surface_finite_variety|reflexivity].
Qed.
End SurfaceAnalytic.

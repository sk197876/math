(** Federer (1969), 3.4.10, p. 338:
    the cited surface has dimension at most two.
    Its actual nonzero global polynomial supplies
    the local depth bound, and the original
    bounded supremum attains its value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness AnalyticSetLocalDepth AnalyticSetDimension
  BoundedNaturalSupremumUP AnalyticZeroLocusDepthBound
  BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed BruhatWhitneySurfaceAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_surface_contains_origin]: the
    actual origin belongs to the surface in
    Bruhat and Whitney, section 11(c), p. 159,
    cited in 3.4.10, p. 338. *)
Lemma bruhat_whitney_surface_contains_origin (R:realType):
  @BruhatWhitneySurface.set R 0.
Proof.
apply/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R)).
rewrite !ffunE;ring.
Qed.

(** Source for [bruhat_whitney_equation_nonzero_value]: the
    original polynomial has value one at
    (1,0,0), supporting the dimension bound
    for the example in 3.4.10, p. 338. *)
Lemma bruhat_whitney_equation_nonzero_value (R:realType):
  @bruhat_whitney_surface_equation R (@coordinate_basis R 3 ord0)= 1.
Proof.
rewrite /bruhat_whitney_surface_equation /coordinate_basis !ffunE /=;ring.
Qed.

(** Source for [bruhat_whitney_dimension_upper]: the
    actual opaque dimension of the cited surface
    is at most two, 3.4.10, p. 338.
    Every local dimension is bounded using the
    original polynomial; no dimension conclusion is assumed. *)
Theorem bruhat_whitney_dimension_upper (R:realType):
  (@analytic_set_dimension R 3 (@BruhatWhitneySurface.set R)<=2)%N.
Proof.
pose S:=@BruhatWhitneySurface.set R.
have hNonempty:S<>set0.
  move=>hEmpty;have h:=@bruhat_whitney_surface_contains_origin R.
  change (S 0) in h;by rewrite hEmpty in h.
have [a [ha hDimension]]:=@bounded_natural_supremum_attained (R_n R 3) S
  (@analytic_set_local_depth R 3 S) (@analytic_set_dimension R 3 S)
  (@analytic_set_dimension_laws R 3 S) hNonempty.
rewrite -hDimension.
have hNonzero:exists b,@bruhat_whitney_surface_equation R b<>0.
  exists (@coordinate_basis R 3 ord0);rewrite bruhat_whitney_equation_nonzero_value.
  by move/eqP;rewrite oner_eq0.
have hZero x:S x ->@bruhat_whitney_surface_equation R x=0.
  exact:(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R) x).1.
have hBound:=@analytic_zero_locus_local_depth_lt R 2 S
  (@bruhat_whitney_surface_equation R) (@bruhat_whitney_surface_equation_analytic R)
  hNonzero hZero a ha.
by move:hBound;rewrite ltnS.
Qed.

(** Federer (1969), 1.7.1, p. 28: bounded compactness implies finite
    dimension. Here a finite-cover argument gives the same obstruction
    without choosing an infinite sequence. Source context: InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp Require Import boolp classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerBoundedness InnerOrthogonality InnerNormalization
  OrthonormalFamilies OrthonormalProjection OrthonormalisationUP GramSchmidt
  FiniteSpans FiniteBasisCriterion LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactDimension.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).

(** Source for [inner_compact_unit_ball_finite_basis]: Federer
    1.7.1, p. 28, reverse implication. A finite cover of the unit ball
    by balls of radius one half supplies a finite spanning family:
    otherwise a normalised orthogonal residual contradicts the cover. *)
Theorem inner_compact_unit_ball_finite_basis : compact (@inner_unit_ball R V B hB) ->
  exists n (e : 'I_n -> V), is_basis e.
Proof.
move=> hc.
have hp : 0 < (2 : R)^-1 by rewrite invr_gt0 ltr0n.
have hopen (z : M) : open (ball z (2 : R)^-1) by exact: ball_open.
have hcover : @inner_unit_ball R V B hB `<=` cover [set: M] (fun z => ball z (2 : R)^-1).
  move=> x hx; exists x; first by [].
  exact: ballxx.
rewrite compact_cover in hc.
have [E _ hE] := hc _ setT (fun z : M => ball z (2 : R)^-1)
  (fun z _ => hopen z) hcover.
have [n [u [hu hspan]]] := @finite_independent_span R V (enum_fset E).
have [e he] := gram_schmidt_exists hB hu.
have ho := orthonormalisation_orthonormal he.
exists n, e; apply: finite_basis_criterion.
- exact (@orthonormal_independent R V B hB (Finite.clone 'I_n _) e ho).
- move=> x; apply: contrapT => hx.
  have hn := @orthonormal_residual_nonzero R V B hB n e x hx.
  pose w : M := inner_normalize hB (x - orthonormal_projection hB e x).
  have hw : inner_norm hB w = 1 by exact: inner_normalize_norm.
  have hwe i : B w (e i) = 0.
    apply: inner_normalize_orthogonal.
    exact (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_n _) e ho x i).
  have hwb : @inner_unit_ball R V B hB w by rewrite /inner_unit_ball /= hw.
  have [z hz hzw] := hE w hwb.
  have hsz : in_finite_span e z.
    apply: (proj1 (@orthonormalisation_span R V B n u e he z)).
    apply: hspan; exact: hz.
  have hwz : B w z = 0 := inner_orthogonal_span hB hwe hsz.
  have hd := @inner_unit_orthogonal_distance R V B hB w z hw hwz.
  have hlt : inner_norm hB (w-z) < (2 : R)^-1.
    move: hzw; rewrite ballEmdist.
    change (inner_norm hB (z-w) < (2 : R)^-1 -> inner_norm hB (w-z) < (2 : R)^-1).
    by rewrite -[z-w]opprB inner_normN.
  have hbad := le_lt_trans hd hlt.
  move: hbad; by rewrite invf_gt1 ?ltr0n // ltrn1.
Qed.

(** Source for [inner_boundedly_compact_finite_basis]: Federer
    1.7.1, p. 28, a boundedly compact inner-product space has a finite
    basis because its closed unit ball is compact. *)
Theorem inner_boundedly_compact_finite_basis : inner_boundedly_compact hB ->
  exists n (e : 'I_n -> V), is_basis e.
Proof. move=> h; apply: inner_compact_unit_ball_finite_basis; exact: inner_unit_ball_compact h. Qed.
End CompactDimension.

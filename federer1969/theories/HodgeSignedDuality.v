(** Federer (1969), 1.7.8, p. 34: the two complementary signs add to p(n-p),
    yielding the square of the Hodge map. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  InnerExteriorBasis OrthonormalFamilies LinearBasis ExteriorGrading
  AlternatingCoordinates FiniteExteriorPowers CovectorProducts
  DualityMaps DualityBasis TopComplements InteriorSigns InteriorComplements
  ExteriorHomogeneousProducts HodgeMaps HodgeBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SignedDuality.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation E := (e_lambda e (val (Lambda_top n))).
Local Notation omega := (fun i => inner_polarity hB (e i)).
Local Notation Omega := (omega_lambda h2 omega (Lambda_top n)).

(** Source for [hodge_polarity_signed_duality]: Federer 1.7.8,
    p. 34, supporting relation between gamma after star and
    D_p: the sign is (-1) to the power p(n-p), because M+N=p(n-p). *)
Theorem hodge_polarity_signed_duality p (hp : (p <= n)%N)
    (x : exterior_power V p) :
  inner_exterior_form h2 hB (hodge_vector h2 hB E hp x) =
    (-1 : R)^+(p*(n-p)) *: D_p Omega hp x.
Proof.
move: x; apply: (basis_induction (finite_e_lambda_basis he h2 p)).
- by rewrite !linear0 ?scaler0.
- move=> x y hx hy; rewrite !linearD ?scalerDr.
  exact (congr2 +%R hx hy).
- move=> c x hx; rewrite !linearZ.
  have hh := congr1 (fun z : A_m V R^o (n-p) => c *: z) hx.
  exact hh.
- move=> lambda.
  have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
    by rewrite inner_polarityE ho eq_sym.
  rewrite -hodge_polarity_diagram inner_exterior_basis_covectors
    (hodge_covector_basis h2 hB he ho)
    (@D_p_basis R h2 V n e omega he hd p hp lambda) scalerA.
  have hs := @FedererInteriorSigns.M_add_N n p (n-p) lambda
    (top_complement lambda) (top_complement_disjoint lambda).
  rewrite -hs exprD mulrAC -exprMn mulrNN mul1r expr1n mul1r.
  by [].
Qed.

(** Source for [hodge_vector_square_basis_volume]: Federer 1.7.8,
    p. 34, star star xi = (-1)^{p(n-p)} xi for the volume
    of an orthonormal basis. The reindexing identifies n-(n-p) with p. *)
Theorem hodge_vector_square_basis_volume p (hp : (p <= n)%N)
    (x : exterior_power V p) :
  exterior_reindex (subKn hp)
    (hodge_vector h2 hB E (leq_subr p n) (hodge_vector h2 hB E hp x)) =
    (-1 : R)^+(p*(n-p)) *: x.
Proof.
change (exterior_reindex (subKn hp)
  (D_upper h2 E (leq_subr p n)
    (inner_exterior_form h2 hB (hodge_vector h2 hB E hp x))) =
  (-1 : R)^+(p*(n-p)) *: x).
rewrite hodge_polarity_signed_duality !linearZ.
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
have hk := @D_pK R h2 V n e omega he hd p hp x.
exact (congr1 (fun z : exterior_power V p => (-1 : R)^+(p*(n-p)) *: z) hk).
Qed.
End SignedDuality.

(** Federer (1969), 1.7.8, p. 34: the second row of complementary-basis
    formulas uses the sign M rather than N. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  InnerExteriorBasis OrthonormalFamilies LinearBasis ExteriorGrading
  AlternatingCoordinates FiniteExteriorPowers CovectorProducts
  TopComplements InteriorSigns HodgeMaps HodgeBasis HodgeSignedDuality
  HodgeAlgebraCompatibility ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Reverse.
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

(** Source for [hodge_vector_complement_basis]: Federer 1.7.8,
    p. 34, star(e_nu)=(-1)^M e_lambda for complementary indices.
    The reindexing identifies n-(n-p) with p. *)
Theorem hodge_vector_complement_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  exterior_reindex (subKn hp) (hodge_vector h2 hB E (leq_subr p n)
    (e_lambda e (val (top_complement lambda)))) =
  (-1 : R)^+(FedererInteriorSigns.M lambda (top_complement lambda)) *:
    e_lambda e (val lambda).
Proof.
have hh := @hodge_vector_square_basis_volume R h2 V B hB n e he ho p hp
  (e_lambda e (val lambda)).
rewrite (@hodge_vector_basis R h2 V B hB n e he ho p hp lambda) !linearZ in hh.
have hs := congr1 (fun z : exterior_power V p =>
  (-1 : R)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *: z) hh.
have hMN := @FedererInteriorSigns.M_add_N n p (n-p) lambda
  (top_complement lambda) (top_complement_disjoint lambda).
have hsign : (-1 : R)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *
    (-1 : R)^+(p*(n-p)) = (-1 : R)^+(FedererInteriorSigns.M lambda (top_complement lambda)).
  by rewrite -hMN exprD mulrCA -exprMn mulrNN mul1r expr1n mulr1.
by rewrite !scalerA -exprMn mulrNN mul1r expr1n scale1r hsign in hs.
Qed.

(** Source for [hodge_covector_complement_basis]: Federer 1.7.8,
    p. 34, star(omega_nu)=(-1)^M omega_lambda, the fourth
    complementary-basis formula. *)
Theorem hodge_covector_complement_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  form_reindex (subKn hp) (hodge_covector h2 hB E (leq_subr p n)
    (omega_lambda h2 omega (top_complement lambda))) =
  (-1 : R)^+(FedererInteriorSigns.M lambda (top_complement lambda)) *:
    omega_lambda h2 omega lambda.
Proof.
rewrite -(@inner_exterior_basis_covectors R h2 V B hB n e (n-p) (top_complement lambda))
  hodge_polarity_diagram inner_exterior_form_reindex
  (hodge_vector_complement_basis hp lambda) linearZ.
exact (congr1 (fun z : A_m V R^o p =>
  (-1 : R)^+(FedererInteriorSigns.M lambda (top_complement lambda)) *: z)
  (@inner_exterior_basis_covectors R h2 V B hB n e p lambda)).
Qed.
End Reverse.

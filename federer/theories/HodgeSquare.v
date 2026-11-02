(** Federer (1969), 1.7.8, p. 34: applying star twice gives the sign
    (-1)^{p(n-p)}, for every unit volume vector. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorIsomorphism
  LinearBasis OrthonormalFamilies GramSchmidt OrthonormalisationUP ExteriorGrading ExteriorNorm
  ExteriorHomogeneousProducts FiniteExteriorPowers TopComplements
  AlternatingCoordinates HodgeMaps HodgeSignedDuality UnitTopVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_vector_square]: Federer 1.7.8,
    p. 34, first conclusion: star star xi = (-1)^{p(n-p)} xi.
    Any unit volume is allowed, including both signs in dimension zero. *)
Theorem hodge_vector_square (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    p (hp : (p <= n)%N) (x : exterior_power V p) :
  exterior_reindex (subKn hp)
    (hodge_vector h2 hB E (leq_subr p n) (hodge_vector h2 hB E hp x)) =
    (-1 : R)^+(p*(n-p)) *: x.
Proof.
have [e [he horth]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal horth.
have [c [hc hc2]] := @unit_top_volume_scalar R h2 V B hB n e he ho E hE.
rewrite hc !hodge_vector_volume_scale !linearZ.
change (c *: (c *: exterior_reindex (subKn hp)
  (hodge_vector h2 hB (e_lambda e (ord_tuple n)) (leq_subr p n)
    (hodge_vector h2 hB (e_lambda e (ord_tuple n)) hp x))) =
  (-1 : R)^+(p*(n-p)) *: x).
rewrite scalerA -expr2 hc2 scale1r.
exact: (@hodge_vector_square_basis_volume R h2 V B hB n e he ho p hp x).
Qed.

(** Source for [hodge_covector_square]: Federer 1.7.8,
    p. 34, third conclusion: star star phi = (-1)^{p(n-p)} phi.
    Transfer through gamma uses only its proved finite-dimensional inverse. *)
Theorem hodge_covector_square (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    p (hp : (p <= n)%N) (phi : A_m V R^o p) :
  form_reindex (subKn hp)
    (hodge_covector h2 hB E (leq_subr p n) (hodge_covector h2 hB E hp phi)) =
    (-1 : R)^+(p*(n-p)) *: phi.
Proof.
have [g [_ hgi]] := @inner_exterior_inverse_exists R h2 V B hB n b hb p.
rewrite -(hgi phi) !hodge_polarity_diagram.
have hr (q r : nat) (h : q=r) (z : exterior_power V q) :
    form_reindex h (inner_exterior_form h2 hB z) =
    inner_exterior_form h2 hB (exterior_reindex h z) by case: r / h.
rewrite hr (@hodge_vector_square R h2 V B hB n b hb E hE p hp (g phi)) linearZ.
by [].
Qed.

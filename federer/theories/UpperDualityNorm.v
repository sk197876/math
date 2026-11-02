(** Federer (1969), 1.7.11, p. 36: supporting metric form of the duality
    reduction, using the Hodge isometry of 1.7.8, p. 34. The local erratum
    has no correction to p. 36. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior ExteriorNorm
  ExteriorCovectorInner LinearBasis ExteriorGrading AlternatingCoordinates
  DualityMaps HodgeMaps HodgeIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [upper_duality_norm]: Federer 1.7.11, p. 36,
    supporting consequence of 1.7.8, p. 34: contraction of a
    unit top vector by a covector preserves the covector norm.
    This follows from the covector Hodge isometry and the polarity
    isometry, and includes degree zero and top degree. *)
Theorem upper_duality_norm (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (E : exterior_power V n)
    (hE : exterior_norm h2 hB E = 1) p (hp : (p <= n)%N)
    (phi : A_m V R^o p) :
  exterior_norm h2 hB (D_upper h2 E hp phi) =
    exterior_covector_norm h2 hB hb phi.
Proof.
rewrite -(@inner_exterior_form_norm R h2 V B hB n b hb (n-p)).
exact (@hodge_covector_norm R h2 V B hB n b hb E hE p hp phi).
Qed.

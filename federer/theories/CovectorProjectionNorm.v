(** Federer (1969), 1.7.7, p. 34, last formula: covector pullback along
    orthogonal injections contracts norms, and a suitable injection attains
    the norm of a nonzero simple covector. The proof transfers the vector
    argument through the abstract polarity isometry, following the book's
    "Similarly". *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm LinearBasis OrthogonalMaps
  AdjointUP Adjoint ExteriorAdjoint ExteriorGrading ExteriorMaps
  InnerExterior InnerExteriorIsomorphism ExteriorCovectorInner
  ExteriorProjectionNorm ExteriorNorm SimplePolarityTransfer
  SimpleProjectionAttainment SimpleCovectors AssociatedSubspace
  AlternatingCoordinates AlternatingDual EuclideanInnerProduct
  GrassmannAbbreviations FiniteCoordinates CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_covector_pullback_bound]: Federer 1.7.7,
    p. 34, the upper-bound half of the covector supremum formula.
    This holds for arbitrary covectors, including zero. *)
Theorem orthogonal_covector_pullback_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n k (b : 'I_n -> V) (e : 'I_k -> U) (hb : is_basis b) (he : is_basis e)
    (f : {linear V -> U}) (hf : is_orthogonal_map B C f)
    m (phi : A_m U R^o m) :
  exterior_covector_norm h2 hB hb (A_m_dual f phi) <= exterior_covector_norm h2 hC he phi.
Proof.
have [g [hg hgi]] := @inner_exterior_inverse_exists R h2 U C hC k e he m.
pose a := inner_adjoint hB hC hb f.
have ha : is_adjoint B C f a := inner_adjointP _ _ _ _.
have hp : is_orthogonal_projection C B a by exists f.
rewrite -(hgi phi) (@adjoint_inner_exterior_form_diagram R h2 V U B C hB hC f a ha m)
  !inner_exterior_form_norm.
exact: (@exterior_projection_norm_bound R h2 U V C B hC hB a hp m (g phi)).
Qed.

(** Source for [simple_covector_pullback_attained]: Federer 1.7.7,
    p. 34, a nonzero simple m-covector attains its norm after
    pullback along some orthogonal injection from R^m. *)
Theorem simple_covector_pullback_attained (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    m (phi : A_m V R^o m) (hp : phi != 0) (sp : simple_covector h2 phi) :
  exists f : {linear R_n R m -> V},
    is_orthogonal_map (@euclidean_inner_product R m) B f /\
    exterior_covector_norm h2 (@euclidean_inner_productP R m) (@coordinate_basisP R m)
      (A_m_dual f phi) = exterior_covector_norm h2 hB hb phi.
Proof.
have [x [sx hx]] := simple_covector_polarity_preimage hB hb sp.
have hn : x != 0 by apply/eqP=> hz; move: hp; rewrite -hx hz linear0 eqxx.
have [f [p [hf [ha hN]]]] := simple_projection_norm_attained h2 hB hn sx.
exists f; split=> //.
rewrite -hx (@adjoint_inner_exterior_form_diagram R h2 (R_n R m) V
  (@euclidean_inner_product R m) B (@euclidean_inner_productP R m) hB f p ha m)
  !inner_exterior_form_norm.
exact hN.
Qed.

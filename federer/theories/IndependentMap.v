(** Federer (1969), 1.7.4, p. 31, penultimate paragraph: a coordinate
    projection restricts to an isomorphism on W. Supporting criterion:
    independent images of a basis imply injectivity. editions:
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteIndependence
  FiniteDualDimension Annihilator Hom BasisInterpolation TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [independent_basis_image_injective]: Federer
    1.7.4, p. 31, supporting injectivity of the restriction of
    p_lambda to W once its basis images have nonzero exterior product. *)
Theorem independent_basis_image_injective (R : fieldType)
    (V U : lmodType R) n (e : 'I_n -> V) (he : is_basis e)
    (f : {linear V -> U}) (hf : finite_independent (fun i => f (e i))) :
  injective f.
Proof.
have hker x : f x = 0 -> x = 0.
  move=> hx.
  have hh := congr1 f (basis_vector_expansion he x).
  rewrite linear_sum hx in hh.
  have heq : (\sum_i f (dual_basis he i x *: e i)) =
      \sum_i dual_basis he i x *: f (e i).
    apply: eq_bigr => i _; exact: linearZ.
  rewrite heq in hh.
  have hs := esym hh.
  have hc := hf _ hs.
  rewrite (basis_vector_expansion he x); apply: big1 => i _.
  by rewrite hc scale0r.
move=> x y hxy; apply/eqP; rewrite -subr_eq0; apply/eqP/hker.
by rewrite linearB hxy subrr.
Qed.

(** Source for [basis_image_inverse_exists]: Federer 1.7.4,
    p. 31, supporting isomorphism assertion: a map taking a basis
    to a basis has a two-sided linear inverse. *)
Theorem basis_image_inverse_exists (R : fieldType) (I : choiceType)
    (V U : lmodType R) (e : I -> V) (he : is_basis e)
    (f : {linear V -> U}) (hf : is_basis (fun i => f (e i))) :
  exists g : {linear U -> V}, cancel f g /\ cancel g f.
Proof.
pose g := basis_interpolation hf e.
exists g; split.
- apply: (basis_linear_ext he (linear_comp g f) (linear_id V)) => i.
  change (g (f (e i)) = e i); exact: basis_interpolationE.
- apply: (basis_linear_ext hf (linear_comp f g) (linear_id U)) => i.
  change (f (g (f (e i))) = f (e i)).
  by rewrite /g basis_interpolationE.
Qed.

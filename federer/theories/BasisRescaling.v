(** Federer (1969), 1.10.2, p. 45: dividing each monomial basis vector by
    its nonzero multiindex factorial preserves a basis. This supporting
    rescaling lemma is stated for arbitrary basis index sets. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear LinearBasis BasisInterpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Rescaling.
Variable K : fieldType.
Variable I : choiceType.
Variable V : lmodType K.
Variable e : I -> V.
Hypothesis he : is_basis e.
Variable r : I -> K.
Hypothesis hr : forall i, r i != 0.

(** Source for [basis_rescale_map]: Federer 1.10.2, p. 45,
    supporting map rescaling each basis vector by its prescribed factor. *)
Definition basis_rescale_map : {linear V -> V} :=
  basis_interpolation he (fun i => r i *: e i).

(** Source for [basis_rescale_inverse]: Federer 1.10.2, p. 45,
    the inverse rescales each basis vector by the reciprocal factor. *)
Definition basis_rescale_inverse : {linear V -> V} :=
  basis_interpolation he (fun i => (r i)^-1 *: e i).

(** Source for [basis_rescale_mapK]: Federer 1.10.2, p. 45,
    supporting cancellation of the two rescalings. *)
Lemma basis_rescale_mapK : cancel basis_rescale_map basis_rescale_inverse.
Proof.
apply: (basis_linear_ext he (linear_comp basis_rescale_inverse basis_rescale_map)
  (linear_id V))=> i.
change (basis_rescale_inverse (basis_rescale_map (e i)) = e i).
rewrite /basis_rescale_map basis_interpolationE linearZ
  /basis_rescale_inverse basis_interpolationE.
change (r i *: ((r i)^-1 *: e i) = e i).
by rewrite scalerA mulfV // scale1r.
Qed.

(** Source for [basis_rescale_inverseK]: Federer 1.10.2, p. 45,
    supporting cancellation in the opposite order. *)
Lemma basis_rescale_inverseK : cancel basis_rescale_inverse basis_rescale_map.
Proof.
apply: (basis_linear_ext he (linear_comp basis_rescale_map basis_rescale_inverse)
  (linear_id V))=> i.
change (basis_rescale_map (basis_rescale_inverse (e i)) = e i).
rewrite /basis_rescale_inverse basis_interpolationE linearZ
  /basis_rescale_map basis_interpolationE.
change ((r i)^-1 *: (r i *: e i) = e i).
by rewrite scalerA mulVf // scale1r.
Qed.

(** Source for [basis_rescaling]: Federer 1.10.2, p. 45,
    supporting consequence: rescaling every basis vector by a nonzero
    scalar gives a basis. Used with inverse factorials. *)
Theorem basis_rescaling : is_basis (fun i => r i *: e i).
Proof.
have hb := basis_transport basis_rescale_mapK basis_rescale_inverseK he.
apply: basis_congr _ hb=> i; by rewrite /basis_rescale_map basis_interpolationE.
Qed.
End Rescaling.

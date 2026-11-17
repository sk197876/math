(** Prescribed first-block diagonal maps for the coefficient
    comparison in Federer (1969), 3.2.45,
    pp. 279–280. Reuse the
    actual diagonal maps and determinant laws
    of 2.7.16(1), p. 135. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_prefix_stretch_zero]: supporting
    empty first-block endpoint for the anisotropic
    argument in Federer 3.2.45,
    pp. 279–280. Scaling no
    coordinates gives the actual identity, including
    an empty whole ambient space. *)
Lemma euclidean_prefix_stretch_zero (R : realType) n (t : R) (x : R_n R n) :
  @euclidean_diagonal_map R n (fun j => if (j<0)%N then t else 1) x=x.
Proof. by apply/ffunP=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE ltn0 mul1r. Qed.

(** Source for [euclidean_prefix_stretch_successor]: supporting
    iteration of the actual coordinate stretches for
    Federer 3.2.45, pp. 279–280.
    Scaling the first r+1 coordinates is
    scaling the first r and then
    its next coordinate. This proves the
    supplied coordinate equation directly from the
    original diagonal-map formula, with no intrinsic
    inequality as a hypothesis. *)
Lemma euclidean_prefix_stretch_successor (R : realType) n r (t : R) (hRN : (r<n)%N)
    (x : R_n R n) :
  @euclidean_diagonal_map R n (fun j => if (j<r.+1)%N then t else 1) x=
    @euclidean_diagonal_map R n (fun j => if j==Ordinal hRN then t else 1)
      (@euclidean_diagonal_map R n (fun j => if (j<r)%N then t else 1) x).
Proof.
apply/ffunP=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
have hIndex : (j==Ordinal hRN)=((j:nat)==r).
  apply/idP/idP=> /eqP h; apply/eqP.
  - exact (congr1 val h).
  - apply: val_inj; exact h.
rewrite hIndex ltnS leq_eqVlt.
case hEqual : ((j:nat)==r).
- by rewrite (eqP hEqual) ltnn /= mul1r.
- by rewrite /= mul1r.
Qed.

(** Source for [euclidean_prefix_stretch_determinant]: supporting
    exact determinant normalization of the anisotropic
    Steiner polynomials in Federer 3.2.45,
    pp. 279–280. The first
    m coordinates are scaled by t
    and the final n are fixed,
    so the existing diagonal determinant is
    t^m. Empty blocks, t=0
    and negative scalars remain. *)
Theorem euclidean_prefix_stretch_determinant (R : realType) m n (t : R) :
  euclidean_det (@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then t else 1))=t^+m.
Proof.
rewrite euclidean_diagonal_det big_split_ord.
have hLeft : (\prod_(i : 'I_m) (if (lshift n i<m)%N then t else 1))=t^+m.
  rewrite (eq_bigr (fun _ : 'I_m => t)); last first.
    move=> i _; change ((if (i<m)%N then t else 1)=t); by rewrite ltn_ord.
  by rewrite prodr_const card_ord.
have hRight : (\prod_(j : 'I_n) (if (rshift m j<m)%N then t else 1))= 1.
  apply: big1=> j _.
  have hNo : (rshift m j<m)%N=false.
    change ((m+j<m)%N=false); by rewrite ltnNge leq_addr.
  by rewrite hNo.
rewrite hLeft hRight.
change (t^+m*1=t^+m); exact: mulr1.
Qed.

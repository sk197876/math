(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:sv: sealed choice of the number sv_m(X). Only the number and its
    characteristic property are exported; the supremum construction of
    DgprSingularValueConstruction.v is hidden. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import InnerProductUP LinearBasis Hom.
From DPGPR Require Import DgprSingularValueUP DgprSingularValueConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type DgprSingularValueSig.
(** Source for [value]: blueprint def:sv, the number sv_m(X) for
    X in Hom(V,W), 1 <= m <= n, and a basis of V with n members. *)
Parameter value : forall (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m <= n)%N)
    (X : Hom V W), R.
(** Source for [laws]: blueprint def:sv, the exported number is the
    supremum characterised in DgprSingularValueUP.v. *)
Parameter laws : forall (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m <= n)%N)
    (X : Hom V W),
  is_dgpr_sv hB hC m X (@value R V W B C hB hC n e he m hm X).
End DgprSingularValueSig.

Module DgprSingularValue : DgprSingularValueSig.
(** Source for [value]: blueprint def:sv, choose the proved
    supremum inside an opaque module. *)
Definition value (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m <= n)%N)
    (X : Hom V W) :=
  sval (constructive_indefinite_description (dgpr_sv_exists hB hC he hm X)).
(** Source for [laws]: blueprint def:sv, the selected number satisfies
    the characteristic property. *)
Lemma laws (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m <= n)%N)
    (X : Hom V W) :
  is_dgpr_sv hB hC m X (@value R V W B C hB hC n e he m hm X).
Proof. exact: (svalP (constructive_indefinite_description (dgpr_sv_exists hB hC he hm X))). Qed.
End DgprSingularValue.

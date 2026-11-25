(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(6),
    pp. 326, 328: the original prefix inclusion has zero tail
    coordinates and fixes every vector with zero tail. This
    scalar-independent connection reuses basis expansion and the
    exact original prefix laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom TensorUP Bilinear LinearBasis FiniteDualDimension Annihilator DualityAnnihilator FiniteCoordinates
  FieldPrefixCoordinatesUP FieldPrefixBasisValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Support.
Variable K:fieldType.
Variable X:lmodType K.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X K^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable p:nat.
Variable hPN:(p<=n)%N.
Variable P:Hom X (coordinate_space K p).
Variable S:Hom (coordinate_space K p) X.
Variable hP:is_field_prefix_projection omega hPN P.
Variable hS:is_field_prefix_section e hPN S.

(** Source for [field_prefix_section_tail_zero]: each original
    included prefix has all omitted coordinates zero,
    3.4.12, p. 339. *)
Lemma field_prefix_section_tail_zero (i:'I_n):
  (p<=i)%N ->forall y,omega i (S y)=0.
Proof.
move=>hPI.
apply:(@basis_induction K (Choice.clone 'I_p _) (coordinate_space K p) (@coordinate_basis K p)
  (@coordinate_basisP K p) (fun y=>omega i (S y)=0)).
- by rewrite !linear0.
- move=>u v hu hv;rewrite !linearD /=.
  change (omega i (S u)+omega i (S v)=0);by rewrite hu hv addr0.
- move=>c u hu;rewrite !linearZ /=.
  change (c*omega i (S u)=0);by rewrite hu mulr0.
- move=>j;rewrite hS hDual.
have hDifferent:i!=widen_ord hPN j.
  apply/eqP=>hEqual.
  have hValues:(i:nat)=(j:nat):=congr1 (fun t:'I_n=>(t:nat)) hEqual.
  have hSmall:(i<p)%N by rewrite hValues;exact:ltn_ord j.
  have hFalse:=leq_ltn_trans hPI hSmall;by rewrite ltnn in hFalse.
by rewrite (negbTE hDifferent).
Qed.

(** Source for [field_prefix_projection_fixed_support]: a vector
    with zero original tail equals the inclusion of its exact
    original prefix, 3.4.12, p. 339. *)
Lemma field_prefix_projection_fixed_support (x:X):
  (forall i:'I_n,(p<=i)%N ->omega i x=0) ->S (P x)=x.
Proof.
move=>hTail.
pose T:=hom_comp S P.
have hOmega i:omega i=dual_basis he i:=biorthogonal_basis_unique he hDual i.
have hOnBasis i:(dual_basis he i x:K)*:T (e i)=(dual_basis he i x:K)*:e i.
  case:(ltnP i p)=>hIP.
  - pose j:'I_p:=Ordinal hIP.
    have hIndex:widen_ord hPN j = i by apply:val_inj.
    rewrite /T hom_compE -hIndex (@field_prefix_basis_inside K X n e omega p hPN P hP hDual j) hS;by [].
  - have hZero:dual_basis he i x=0 by rewrite -(hOmega i);exact:hTail.
    by rewrite hZero !scale0r.
have hExpansion:=basis_vector_expansion he x.
have hImage:T x=\sum_i (dual_basis he i x:K)*:T (e i).
  rewrite {1}hExpansion (big_morph T (linD (hom_linear T)) (lin0 (hom_linear T))).
  apply:eq_bigr=>i _;exact:(linZ (hom_linear T)).
change (T x=x);rewrite hImage [RHS]hExpansion.
apply:eq_bigr=>i _;exact:hOnBasis.
Qed.
End Support.
